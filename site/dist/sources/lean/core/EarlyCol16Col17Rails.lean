import EarlyCol15ConstantRail

set_option autoImplicit false

namespace ChompLean

/-!
# Constant column-sixteen and affine column-seventeen rails

The finite windows are discharged directly from the positive-MEX recurrence.
The local simp set below contains only previously certified closed cells and
fixed-column rails; it is used to normalize the finite source checks.
-/

attribute [local simp]
  gameF_col0 gameF_col1_rail gameF_col2_rail gameF_col3_rail
  gameF_col4_rail gameF_col5_rail gameF_col6_rail gameF_col7_rail
  gameF_col8_rail gameF_col9_rail gameF_col10_rail gameF_col11_rail
  gameF_col12_rail gameF_col13_rail gameF_col14_rail gameF_col15_rail
  gameF_zero_zero gameF_one_one gameF_diag_two gameF_diag_three
  gameF_diag_four gameF_diag_five gameF_diag_six gameF_seven_seven
  gameF_diag_eight gameF_diag_nine gameF_diag_ten gameF_diag_eleven
  gameF_diag_twelve gameF_diag_thirteen gameF_diag_fourteen
  gameF_diag_fifteen
  gameF_four_three gameF_five_three
  gameF_five_four gameF_six_four gameF_six_five gameF_seven_four
  gameF_seven_six gameF_eight_six gameF_nine_six
  gameF_eight_seven gameF_nine_seven
  gameF_nine_eight gameF_ten_eight gameF_eleven_eight
  gameF_twelve_eight gameF_ten_nine gameF_eleven_nine
  gameF_eleven_ten gameF_twelve_ten gameF_thirteen_ten
  gameF_fourteen_ten
  gameF_twelve_eleven gameF_thirteen_eleven gameF_fourteen_eleven
  gameF_fifteen_eleven gameF_sixteen_eleven gameF_seventeen_eleven
  gameF_eighteen_eleven
  gameF_thirteen_twelve gameF_fourteen_twelve gameF_fifteen_twelve
  gameF_sixteen_twelve gameF_seventeen_twelve
  gameF_fourteen_thirteen gameF_fifteen_thirteen gameF_sixteen_thirteen
  gameF_seventeen_thirteen gameF_eighteen_thirteen gameF_nineteen_thirteen
  gameF_fifteen_fourteen gameF_sixteen_fourteen gameF_seventeen_fourteen
  gameF_eighteen_fourteen gameF_nineteen_fourteen gameF_twenty_fourteen
  gameF_sixteen_fifteen gameF_seventeen_fifteen gameF_eighteen_fifteen
  gameF_nineteen_fifteen gameF_twenty_fifteen gameF_twentyone_fifteen
  gameF_twentytwo_fifteen

/- A bounded brute-force tactic for the finite positive source checks.  Each
candidate is certified by an already proved cell equality. -/
macro "early_source" : tactic =>
  `(tactic|
    first
    | (exact Or.inl ⟨0, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨1, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨2, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨3, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨4, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨5, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨6, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨7, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨8, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨9, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨10, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨11, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨12, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨13, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨14, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨15, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨16, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨17, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨18, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨19, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨20, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨21, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨22, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨23, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨24, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨25, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨26, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨27, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨28, by omega, by simpa⟩; done)
    | (exact Or.inl ⟨29, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨0, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨1, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨2, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨3, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨4, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨5, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨6, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨7, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨8, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨9, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨10, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨11, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨12, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨13, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨14, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨15, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨16, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨17, by omega, by simpa⟩; done)
    | (exact Or.inr ⟨18, by omega, by simpa⟩; done))

macro "early_absent24" : tactic =>
  `(tactic| (
    intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, ha, hv⟩
      have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/
          a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/
          a = 21 \/ a = 22 \/ a = 23 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · rcases hC with ⟨b, hb, hv⟩
      have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/
          b = 16 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all))

macro "early_lower34" : tactic =>
  `(tactic| (
    intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/
        k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> early_source))

/- `d(16)=28`. -/
@[simp] theorem gameF_diag_sixteen : gameF 16 16 = 28 := by
  apply gameF_value_of_source_mex (q := 16) (r := 16) (m := 28)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      early_source

@[simp] theorem gameF_seventeen_sixteen : gameF 17 16 = 29 := by
  apply gameF_value_of_source_mex (q := 17) (r := 16) (m := 29)
  · omega
  · rw [gameF_diag_sixteen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩

@[simp] theorem gameF_eighteen_sixteen : gameF 18 16 = 26 := by
  apply gameF_value_of_source_mex (q := 18) (r := 16) (m := 26)
  · omega
  · rw [gameF_seventeen_sixteen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩

@[simp] theorem gameF_nineteen_sixteen : gameF 19 16 = 31 := by
  apply gameF_value_of_source_mex (q := 19) (r := 16) (m := 31)
  · omega
  · rw [gameF_eighteen_sixteen]; omega
  · omega
  · early_absent24
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
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩

@[simp] theorem gameF_twenty_sixteen : gameF 20 16 = 30 := by
  apply gameF_value_of_source_mex (q := 20) (r := 16) (m := 30)
  · omega
  · rw [gameF_nineteen_sixteen]; omega
  · omega
  · early_absent24
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩

@[simp] theorem gameF_twentyone_sixteen : gameF 21 16 = 32 := by
  apply gameF_value_of_source_mex (q := 21) (r := 16) (m := 32)
  · omega
  · rw [gameF_twenty_sixteen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/
        k = 30 \/ k = 31 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩

@[simp] theorem gameF_twentytwo_sixteen : gameF 22 16 = 33 := by
  apply gameF_value_of_source_mex (q := 22) (r := 16) (m := 33)
  · omega
  · rw [gameF_twentyone_sixteen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/
        k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

/- Freeze cell for column sixteen. -/
@[simp] theorem gameF_twentythree_sixteen : gameF 23 16 = 23 := by
  apply gameF_value_of_source_mex (q := 23) (r := 16) (m := 23)
  · omega
  · rw [gameF_twentytwo_sixteen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
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

/- Constant column-sixteen rail. -/
theorem gameF_col16_rail {q : Nat} (hq : 23 <= q) : gameF q 16 = 23 := by
  have hsmall : gameF 23 16 < 23 + 1 := by
    rw [gameF_twentythree_sixteen]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 23) (r := 16) (by omega) hsmall (q - 23)
  change gameF (23 + (q - 23)) 16 = gameF 23 16 at hconst
  have hsum : 23 + (q - 23) = q := by omega
  rw [hsum, gameF_twentythree_sixteen] at hconst
  exact hconst

attribute [local simp] gameF_col16_rail

/-! ## Column seventeen finite window -/

@[simp] theorem gameF_diag_seventeen : gameF 17 17 = 30 := by
  apply gameF_value_of_source_mex (q := 17) (r := 17) (m := 30)
  · omega
  · omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩

@[simp] theorem gameF_eighteen_seventeen : gameF 18 17 = 31 := by
  apply gameF_value_of_source_mex (q := 18) (r := 17) (m := 31)
  · omega
  · rw [gameF_diag_seventeen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩

@[simp] theorem gameF_nineteen_seventeen : gameF 19 17 = 29 := by
  apply gameF_value_of_source_mex (q := 19) (r := 17) (m := 29)
  · omega
  · rw [gameF_eighteen_seventeen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩

@[simp] theorem gameF_twenty_seventeen : gameF 20 17 = 32 := by
  apply gameF_value_of_source_mex (q := 20) (r := 17) (m := 32)
  · omega
  · rw [gameF_nineteen_seventeen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩

@[simp] theorem gameF_twentyone_seventeen : gameF 21 17 = 33 := by
  apply gameF_value_of_source_mex (q := 21) (r := 17) (m := 33)
  · omega
  · rw [gameF_twenty_seventeen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩

@[simp] theorem gameF_twentytwo_seventeen : gameF 22 17 = 34 := by
  apply gameF_value_of_source_mex (q := 22) (r := 17) (m := 34)
  · omega
  · rw [gameF_twentyone_seventeen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentythree_seventeen : gameF 23 17 = 26 := by
  apply gameF_value_of_source_mex (q := 23) (r := 17) (m := 26)
  · omega
  · rw [gameF_twentytwo_seventeen]; omega
  · omega
  · early_absent24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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



/-- Affine column-seventeen rail: F(q,17)=q+11 for q≥24. -/
theorem gameF_col17_rail {q : Nat} (hq : 24 <= q) : gameF q 17 = q + 11 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 17) (t := 24) (d := 11) (q := q) (by omega) (by omega)
  · rw [gameF_twentythree_seventeen]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
  · exact hq

attribute [local simp] gameF_col17_rail

macro "early_absent27_19" : tactic =>
  `(tactic| (
    intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, ha, hv⟩
      have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/
          a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/
          a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/
          a = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · rcases hC with ⟨b, hb, hv⟩
      have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/
          b = 16 \/ b = 17 \/ b = 18 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> simp_all))


/-! ## Column eighteen finite window -/

@[simp] theorem gameF_diag_eighteen : gameF 18 18 = 32 := by
  apply gameF_value_of_source_mex (q := 18) (r := 18) (m := 32)
  · omega
  · omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩

@[simp] theorem gameF_nineteen_eighteen : gameF 19 18 = 33 := by
  apply gameF_value_of_source_mex (q := 19) (r := 18) (m := 33)
  · omega
  · rw [gameF_diag_eighteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩

@[simp] theorem gameF_twenty_eighteen : gameF 20 18 = 31 := by
  apply gameF_value_of_source_mex (q := 20) (r := 18) (m := 31)
  · omega
  · rw [gameF_nineteen_eighteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩

@[simp] theorem gameF_twentyone_eighteen : gameF 21 18 = 29 := by
  apply gameF_value_of_source_mex (q := 21) (r := 18) (m := 29)
  · omega
  · rw [gameF_twenty_eighteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩

@[simp] theorem gameF_twentytwo_eighteen : gameF 22 18 = 35 := by
  apply gameF_value_of_source_mex (q := 22) (r := 18) (m := 35)
  · omega
  · rw [gameF_twentyone_eighteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩

@[simp] theorem gameF_twentythree_eighteen : gameF 23 18 = 34 := by
  apply gameF_value_of_source_mex (q := 23) (r := 18) (m := 34)
  · omega
  · rw [gameF_twentytwo_eighteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩

@[simp] theorem gameF_twentyfour_eighteen : gameF 24 18 = 36 := by
  apply gameF_value_of_source_mex (q := 24) (r := 18) (m := 36)
  · omega
  · rw [gameF_twentythree_eighteen]; omega
  · omega
  · early_absent27_19
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩

@[simp] theorem gameF_twentyfive_eighteen : gameF 25 18 = 37 := by
  apply gameF_value_of_source_mex (q := 25) (r := 18) (m := 37)
  · omega
  · rw [gameF_twentyfour_eighteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem gameF_twentysix_eighteen : gameF 26 18 = 26 := by
  apply gameF_value_of_source_mex (q := 26) (r := 18) (m := 26)
  · omega
  · rw [gameF_twentyfive_eighteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/- Constant column-eighteen rail. -/
theorem gameF_col18_rail {q : Nat} (hq : 26 <= q) : gameF q 18 = 26 := by
  have hsmall : gameF 26 18 < 26 + 1 := by
    rw [gameF_twentysix_eighteen]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 26) (r := 18) (by omega) hsmall (q - 26)
  change gameF (26 + (q - 26)) 18 = gameF 26 18 at hconst
  have hsum : 26 + (q - 26) = q := by omega
  rw [hsum, gameF_twentysix_eighteen] at hconst
  exact hconst

attribute [local simp] gameF_col18_rail



/-! ## Column nineteen finite window -/

@[simp] theorem gameF_diag_nineteen : gameF 19 19 = 34 := by
  apply gameF_value_of_source_mex (q := 19) (r := 19) (m := 34)
  · omega
  · omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩

@[simp] theorem gameF_twenty_nineteen : gameF 20 19 = 33 := by
  apply gameF_value_of_source_mex (q := 20) (r := 19) (m := 33)
  · omega
  · rw [gameF_diag_nineteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩

@[simp] theorem gameF_twentyone_nineteen : gameF 21 19 = 35 := by
  apply gameF_value_of_source_mex (q := 21) (r := 19) (m := 35)
  · omega
  · rw [gameF_twenty_nineteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩

@[simp] theorem gameF_twentytwo_nineteen : gameF 22 19 = 36 := by
  apply gameF_value_of_source_mex (q := 22) (r := 19) (m := 36)
  · omega
  · rw [gameF_twentyone_nineteen]; omega
  · omega
  · early_absent27_19
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentythree_nineteen : gameF 23 19 = 31 := by
  apply gameF_value_of_source_mex (q := 23) (r := 19) (m := 31)
  · omega
  · rw [gameF_twentytwo_nineteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩

@[simp] theorem gameF_twentyfour_nineteen : gameF 24 19 = 37 := by
  apply gameF_value_of_source_mex (q := 24) (r := 19) (m := 37)
  · omega
  · rw [gameF_twentythree_nineteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩

@[simp] theorem gameF_twentyfive_nineteen : gameF 25 19 = 38 := by
  apply gameF_value_of_source_mex (q := 25) (r := 19) (m := 38)
  · omega
  · rw [gameF_twentyfour_nineteen]; omega
  · omega
  · early_absent27_19
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem gameF_twentysix_nineteen : gameF 26 19 = 29 := by
  apply gameF_value_of_source_mex (q := 26) (r := 19) (m := 29)
  · omega
  · rw [gameF_twentyfive_nineteen]; omega
  · omega
  · early_absent27_19
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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



/-- Affine column-nineteen rail: F(q,19)=q+12 for q≥27. -/
theorem gameF_col19_rail {q : Nat} (hq : 27 <= q) : gameF q 19 = q + 12 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 19) (t := 27) (d := 12) (q := q) (by omega) (by omega)
  · rw [gameF_twentysix_nineteen]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
  · exact hq


attribute [local simp] gameF_col19_rail

macro "early_absent31_22" : tactic =>
  `(tactic| (
    intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, ha, hv⟩
      have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · rcases hC with ⟨b, hb, hv⟩
      have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all))

/-! ## Column twenty finite window -/

@[simp] theorem gameF_diag_twenty : gameF 20 20 = 35 := by
  apply gameF_value_of_source_mex (q := 20) (r := 20) (m := 35)
  · omega
  · omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩

@[simp] theorem gameF_twentyone_twenty : gameF 21 20 = 36 := by
  apply gameF_value_of_source_mex (q := 21) (r := 20) (m := 36)
  · omega
  · rw [gameF_diag_twenty]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩

@[simp] theorem gameF_twentytwo_twenty : gameF 22 20 = 37 := by
  apply gameF_value_of_source_mex (q := 22) (r := 20) (m := 37)
  · omega
  · rw [gameF_twentyone_twenty]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentythree_twenty : gameF 23 20 = 33 := by
  apply gameF_value_of_source_mex (q := 23) (r := 20) (m := 33)
  · omega
  · rw [gameF_twentytwo_twenty]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩

@[simp] theorem gameF_twentyfour_twenty : gameF 24 20 = 38 := by
  apply gameF_value_of_source_mex (q := 24) (r := 20) (m := 38)
  · omega
  · rw [gameF_twentythree_twenty]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩

@[simp] theorem gameF_twentyfive_twenty : gameF 25 20 = 39 := by
  apply gameF_value_of_source_mex (q := 25) (r := 20) (m := 39)
  · omega
  · rw [gameF_twentyfour_twenty]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem gameF_twentysix_twenty : gameF 26 20 = 40 := by
  apply gameF_value_of_source_mex (q := 26) (r := 20) (m := 40)
  · omega
  · rw [gameF_twentyfive_twenty]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩

@[simp] theorem gameF_twentyseven_twenty : gameF 27 20 = 41 := by
  apply gameF_value_of_source_mex (q := 27) (r := 20) (m := 41)
  · omega
  · rw [gameF_twentysix_twenty]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem gameF_twentyeight_twenty : gameF 28 20 = 31 := by
  apply gameF_value_of_source_mex (q := 28) (r := 20) (m := 31)
  · omega
  · rw [gameF_twentyseven_twenty]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

@[simp] theorem gameF_twentynine_twenty : gameF 29 20 = 29 := by
  apply gameF_value_of_source_mex (q := 29) (r := 20) (m := 29)
  · omega
  · rw [gameF_twentyeight_twenty]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/- Constant column-twenty rail. -/
theorem gameF_col20_rail {q : Nat} (hq : 29 <= q) : gameF q 20 = 29 := by
  have hsmall : gameF 29 20 < 29 + 1 := by
    rw [gameF_twentynine_twenty]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 29) (r := 20) (by omega) hsmall (q - 29)
  change gameF (29 + (q - 29)) 20 = gameF 29 20 at hconst
  have hsum : 29 + (q - 29) = q := by omega
  rw [hsum, gameF_twentynine_twenty] at hconst
  exact hconst

attribute [local simp] gameF_col20_rail

/-! ## Column twentyone finite window -/

@[simp] theorem gameF_diag_twentyone : gameF 21 21 = 37 := by
  apply gameF_value_of_source_mex (q := 21) (r := 21) (m := 37)
  · omega
  · omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩

@[simp] theorem gameF_twentytwo_twentyone : gameF 22 21 = 38 := by
  apply gameF_value_of_source_mex (q := 22) (r := 21) (m := 38)
  · omega
  · rw [gameF_diag_twentyone]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentythree_twentyone : gameF 23 21 = 36 := by
  apply gameF_value_of_source_mex (q := 23) (r := 21) (m := 36)
  · omega
  · rw [gameF_twentytwo_twentyone]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩

@[simp] theorem gameF_twentyfour_twentyone : gameF 24 21 = 39 := by
  apply gameF_value_of_source_mex (q := 24) (r := 21) (m := 39)
  · omega
  · rw [gameF_twentythree_twentyone]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩

@[simp] theorem gameF_twentyfive_twentyone : gameF 25 21 = 33 := by
  apply gameF_value_of_source_mex (q := 25) (r := 21) (m := 33)
  · omega
  · rw [gameF_twentyfour_twentyone]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

@[simp] theorem gameF_twentysix_twentyone : gameF 26 21 = 41 := by
  apply gameF_value_of_source_mex (q := 26) (r := 21) (m := 41)
  · omega
  · rw [gameF_twentyfive_twentyone]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩

@[simp] theorem gameF_twentyseven_twentyone : gameF 27 21 = 40 := by
  apply gameF_value_of_source_mex (q := 27) (r := 21) (m := 40)
  · omega
  · rw [gameF_twentysix_twentyone]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem gameF_twentyeight_twentyone : gameF 28 21 = 42 := by
  apply gameF_value_of_source_mex (q := 28) (r := 21) (m := 42)
  · omega
  · rw [gameF_twentyseven_twentyone]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem gameF_twentynine_twentyone : gameF 29 21 = 43 := by
  apply gameF_value_of_source_mex (q := 29) (r := 21) (m := 43)
  · omega
  · rw [gameF_twentyeight_twentyone]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩

@[simp] theorem gameF_thirty_twentyone : gameF 30 21 = 44 := by
  apply gameF_value_of_source_mex (q := 30) (r := 21) (m := 44)
  · omega
  · rw [gameF_twentynine_twentyone]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem gameF_thirtyone_twentyone : gameF 31 21 = 31 := by
  apply gameF_value_of_source_mex (q := 31) (r := 21) (m := 31)
  · omega
  · rw [gameF_thirty_twentyone]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/- Constant column-twentyone rail. -/
theorem gameF_col21_rail {q : Nat} (hq : 31 <= q) : gameF q 21 = 31 := by
  have hsmall : gameF 31 21 < 31 + 1 := by
    rw [gameF_thirtyone_twentyone]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 31) (r := 21) (by omega) hsmall (q - 31)
  change gameF (31 + (q - 31)) 21 = gameF 31 21 at hconst
  have hsum : 31 + (q - 31) = q := by omega
  rw [hsum, gameF_thirtyone_twentyone] at hconst
  exact hconst

attribute [local simp] gameF_col21_rail

/-! ## Column twentytwo finite window -/

@[simp] theorem gameF_diag_twentytwo : gameF 22 22 = 39 := by
  apply gameF_value_of_source_mex (q := 22) (r := 22) (m := 39)
  · omega
  · omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentythree_twentytwo : gameF 23 22 = 38 := by
  apply gameF_value_of_source_mex (q := 23) (r := 22) (m := 38)
  · omega
  · rw [gameF_diag_twentytwo]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentyfour_twentytwo : gameF 24 22 = 40 := by
  apply gameF_value_of_source_mex (q := 24) (r := 22) (m := 40)
  · omega
  · rw [gameF_twentythree_twentytwo]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩

@[simp] theorem gameF_twentyfive_twentytwo : gameF 25 22 = 41 := by
  apply gameF_value_of_source_mex (q := 25) (r := 22) (m := 41)
  · omega
  · rw [gameF_twentyfour_twentytwo]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem gameF_twentysix_twentytwo : gameF 26 22 = 36 := by
  apply gameF_value_of_source_mex (q := 26) (r := 22) (m := 36)
  · omega
  · rw [gameF_twentyfive_twentytwo]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩

@[simp] theorem gameF_twentyseven_twentytwo : gameF 27 22 = 42 := by
  apply gameF_value_of_source_mex (q := 27) (r := 22) (m := 42)
  · omega
  · rw [gameF_twentysix_twentytwo]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩

@[simp] theorem gameF_twentyeight_twentytwo : gameF 28 22 = 43 := by
  apply gameF_value_of_source_mex (q := 28) (r := 22) (m := 43)
  · omega
  · rw [gameF_twentyseven_twentytwo]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩

@[simp] theorem gameF_twentynine_twentytwo : gameF 29 22 = 44 := by
  apply gameF_value_of_source_mex (q := 29) (r := 22) (m := 44)
  · omega
  · rw [gameF_twentyeight_twentytwo]; omega
  · omega
  · early_absent31_22
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
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩

@[simp] theorem gameF_thirty_twentytwo : gameF 30 22 = 33 := by
  apply gameF_value_of_source_mex (q := 30) (r := 22) (m := 33)
  · omega
  · rw [gameF_twentynine_twentytwo]; omega
  · omega
  · early_absent31_22
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- Affine column-twentytwo rail: F(q,22)=q+14 for q≥31. -/
theorem gameF_col22_rail {q : Nat} (hq : 31 <= q) : gameF q 22 = q + 14 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 22) (t := 31) (d := 14) (q := q) (by omega) (by omega)
  · rw [gameF_thirty_twentytwo]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
  · exact hq


attribute [local simp] gameF_col22_rail

macro "early_absent34_24" : tactic =>
  `(tactic| (
    intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, ha, hv⟩
      have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · rcases hC with ⟨b, hb, hv⟩
      have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all))

/-! ## Column twentythree finite window -/

@[simp] theorem gameF_diag_twentythree : gameF 23 23 = 40 := by
  apply gameF_value_of_source_mex (q := 23) (r := 23) (m := 40)
  · omega
  · omega
  · omega
  · early_absent34_24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩

@[simp] theorem gameF_twentyfour_twentythree : gameF 24 23 = 41 := by
  apply gameF_value_of_source_mex (q := 24) (r := 23) (m := 41)
  · omega
  · rw [gameF_diag_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩

@[simp] theorem gameF_twentyfive_twentythree : gameF 25 23 = 42 := by
  apply gameF_value_of_source_mex (q := 25) (r := 23) (m := 42)
  · omega
  · rw [gameF_twentyfour_twentythree]; omega
  · omega
  · early_absent34_24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem gameF_twentysix_twentythree : gameF 26 23 = 38 := by
  apply gameF_value_of_source_mex (q := 26) (r := 23) (m := 38)
  · omega
  · rw [gameF_twentyfive_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentyseven_twentythree : gameF 27 23 = 43 := by
  apply gameF_value_of_source_mex (q := 27) (r := 23) (m := 43)
  · omega
  · rw [gameF_twentysix_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩

@[simp] theorem gameF_twentyeight_twentythree : gameF 28 23 = 36 := by
  apply gameF_value_of_source_mex (q := 28) (r := 23) (m := 36)
  · omega
  · rw [gameF_twentyseven_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩

@[simp] theorem gameF_twentynine_twentythree : gameF 29 23 = 45 := by
  apply gameF_value_of_source_mex (q := 29) (r := 23) (m := 45)
  · omega
  · rw [gameF_twentyeight_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩

@[simp] theorem gameF_thirty_twentythree : gameF 30 23 = 46 := by
  apply gameF_value_of_source_mex (q := 30) (r := 23) (m := 46)
  · omega
  · rw [gameF_twentynine_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem gameF_thirtyone_twentythree : gameF 31 23 = 44 := by
  apply gameF_value_of_source_mex (q := 31) (r := 23) (m := 44)
  · omega
  · rw [gameF_thirty_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩

@[simp] theorem gameF_thirtytwo_twentythree : gameF 32 23 = 47 := by
  apply gameF_value_of_source_mex (q := 32) (r := 23) (m := 47)
  · omega
  · rw [gameF_thirtyone_twentythree]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩

@[simp] theorem gameF_thirtythree_twentythree : gameF 33 23 = 33 := by
  apply gameF_value_of_source_mex (q := 33) (r := 23) (m := 33)
  · omega
  · rw [gameF_thirtytwo_twentythree]; omega
  · omega
  · early_absent34_24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/- Constant column-twentythree rail. -/
theorem gameF_col23_rail {q : Nat} (hq : 33 <= q) : gameF q 23 = 33 := by
  have hsmall : gameF 33 23 < 33 + 1 := by
    rw [gameF_thirtythree_twentythree]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 33) (r := 23) (by omega) hsmall (q - 33)
  change gameF (33 + (q - 33)) 23 = gameF 33 23 at hconst
  have hsum : 33 + (q - 33) = q := by omega
  rw [hsum, gameF_thirtythree_twentythree] at hconst
  exact hconst

attribute [local simp] gameF_col23_rail

/-! ## Column twentyfour finite window -/

@[simp] theorem gameF_diag_twentyfour : gameF 24 24 = 42 := by
  apply gameF_value_of_source_mex (q := 24) (r := 24) (m := 42)
  · omega
  · omega
  · omega
  · early_absent34_24
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩

@[simp] theorem gameF_twentyfive_twentyfour : gameF 25 24 = 43 := by
  apply gameF_value_of_source_mex (q := 25) (r := 24) (m := 43)
  · omega
  · rw [gameF_diag_twentyfour]; omega
  · omega
  · early_absent34_24
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

@[simp] theorem gameF_twentysix_twentyfour : gameF 26 24 = 44 := by
  apply gameF_value_of_source_mex (q := 26) (r := 24) (m := 44)
  · omega
  · rw [gameF_twentyfive_twentyfour]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inl ⟨25, by omega, by simpa⟩

@[simp] theorem gameF_twentyseven_twentyfour : gameF 27 24 = 45 := by
  apply gameF_value_of_source_mex (q := 27) (r := 24) (m := 45)
  · omega
  · rw [gameF_twentysix_twentyfour]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem gameF_twentyeight_twentyfour : gameF 28 24 = 38 := by
  apply gameF_value_of_source_mex (q := 28) (r := 24) (m := 38)
  · omega
  · rw [gameF_twentyseven_twentyfour]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem gameF_twentynine_twentyfour : gameF 29 24 = 46 := by
  apply gameF_value_of_source_mex (q := 29) (r := 24) (m := 46)
  · omega
  · rw [gameF_twentyeight_twentyfour]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩

@[simp] theorem gameF_thirty_twentyfour : gameF 30 24 = 47 := by
  apply gameF_value_of_source_mex (q := 30) (r := 24) (m := 47)
  · omega
  · rw [gameF_twentynine_twentyfour]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem gameF_thirtyone_twentyfour : gameF 31 24 = 41 := by
  apply gameF_value_of_source_mex (q := 31) (r := 24) (m := 41)
  · omega
  · rw [gameF_thirty_twentyfour]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩

@[simp] theorem gameF_thirtytwo_twentyfour : gameF 32 24 = 48 := by
  apply gameF_value_of_source_mex (q := 32) (r := 24) (m := 48)
  · omega
  · rw [gameF_thirtyone_twentyfour]; omega
  · omega
  · early_absent34_24
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
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩

@[simp] theorem gameF_thirtythree_twentyfour : gameF 33 24 = 36 := by
  apply gameF_value_of_source_mex (q := 33) (r := 24) (m := 36)
  · omega
  · rw [gameF_thirtytwo_twentyfour]; omega
  · omega
  · early_absent34_24
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

/-- Affine column-twentyfour rail: F(q,24)=q+15 for q≥34. -/
theorem gameF_col24_rail {q : Nat} (hq : 34 <= q) : gameF q 24 = q + 15 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 24) (t := 34) (d := 15) (q := q) (by omega) (by omega)
  · rw [gameF_thirtythree_twentyfour]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
  · exact hq

#print axioms gameF_col23_rail
#print axioms gameF_col24_rail

#print axioms gameF_col20_rail
#print axioms gameF_col21_rail
#print axioms gameF_col22_rail

#print axioms gameF_col18_rail
#print axioms gameF_col19_rail

#print axioms gameF_col16_rail
#print axioms gameF_col17_rail

end ChompLean
