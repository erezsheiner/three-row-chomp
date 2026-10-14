import R66StageA

/-!
# Exact early rails through column 6

This file proves the finite cells needed to start the column-5 affine rail.
Every finite value is certified directly from `gameF_value_of_source_mex`.
-/

set_option autoImplicit false

namespace ChompLean

/-- The last pre-column-3 base cell. -/
theorem gameF_four_three : gameF 4 3 = 7 := by
  apply gameF_value_of_source_mex (q := 4) (r := 3) (m := 7)
  · omega
  · rw [gameF_diag_three]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 4) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 4) (by omega)] at hval; omega
  · intro k hk0 hk7
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 4) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 4⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩

/-- `d(4)=8`. -/
theorem gameF_diag_four : gameF 4 4 = 8 := by
  apply gameF_value_of_source_mex (q := 4) (r := 4) (m := 8)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 4) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 4) (by omega)] at hval; omega
      · rw [gameF_four_three] at hval; omega
  · intro k hk0 hk8
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 4) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 4⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨3, by omega, gameF_four_three⟩

/-- The freeze cell starting the constant column-3 rail. -/
theorem gameF_five_three : gameF 5 3 = 5 := by
  apply gameF_value_of_source_mex (q := 5) (r := 3) (m := 5)
  · omega
  · rw [gameF_four_three]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_four_three] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 5) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 5) (by omega)] at hval; omega
  · intro k hk0 hk5
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 5) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩

/-- Constant column-3 rail. -/
theorem gameF_col3_rail {q : Nat} (hq : 5 ≤ q) : gameF q 3 = 5 := by
  have hsmall : gameF 5 3 < 5 + 1 := by rw [gameF_five_three]; omega
  have hconst := constant_from gameRecurrenceModel
    (q := 5) (r := 3) (by omega) hsmall (q - 5)
  change gameF (5 + (q - 5)) 3 = gameF 5 3 at hconst
  have hsum : 5 + (q - 5) = q := by omega
  rw [hsum, gameF_five_three] at hconst
  exact hconst

/-- The column-4 cell immediately before `d(5)`. -/
theorem gameF_five_four : gameF 5 4 = 9 := by
  apply gameF_value_of_source_mex (q := 5) (r := 4) (m := 9)
  · omega
  · rw [gameF_diag_four]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 5) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 5) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 5) (by omega)] at hval; omega
  · intro k hk0 hk9
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 5) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 5) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 5) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩

/-- `d(5)=10`. -/
theorem gameF_diag_five : gameF 5 5 = 10 := by
  apply gameF_value_of_source_mex (q := 5) (r := 5) (m := 10)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 5) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 5) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 5) (by omega)] at hval; omega
      · rw [gameF_five_four] at hval; omega
  · intro k hk0 hk10
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 5) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 5) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 5) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨4, by omega, gameF_five_four⟩

/-- The second pre-freeze column-4 cell. -/
theorem gameF_six_four : gameF 6 4 = 10 := by
  apply gameF_value_of_source_mex (q := 6) (r := 4) (m := 10)
  · omega
  · rw [gameF_five_four]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_five_four] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 6) (by omega)] at hval; omega
  · intro k hk0 hk10
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 6) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 6) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 6⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_five_four⟩

/-- The exceptional column-5 cell immediately before the affine rail. -/
theorem gameF_six_five : gameF 6 5 = 9 := by
  apply gameF_value_of_source_mex (q := 6) (r := 5) (m := 9)
  · omega
  · rw [gameF_diag_five]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_six_four] at hval; omega
  · intro k hk0 hk9
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 6) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 6) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 6⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩

/-- The freeze cell starting the constant column-4 rail. -/
theorem gameF_seven_four : gameF 7 4 = 7 := by
  apply gameF_value_of_source_mex (q := 7) (r := 4) (m := 7)
  · omega
  · rw [gameF_six_four]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_five_four] at hval
      · simp [gameF_six_four] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 7) (by omega)] at hval; omega
  · intro k hk0 hk7
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩

/-- Constant column-4 rail. -/
theorem gameF_col4_rail {q : Nat} (hq : 7 ≤ q) : gameF q 4 = 7 := by
  have hsmall : gameF 7 4 < 7 + 1 := by rw [gameF_seven_four]; omega
  have hconst := constant_from gameRecurrenceModel
    (q := 7) (r := 4) (by omega) hsmall (q - 7)
  change gameF (7 + (q - 7)) 4 = gameF 7 4 at hconst
  have hsum : 7 + (q - 7) = q := by omega
  rw [hsum, gameF_seven_four] at hconst
  exact hconst

/-- First affine early rail: `F(q,5)=q+4` for every `q≥7`. -/
theorem gameF_col5_rail {q : Nat} (hq : 7 ≤ q) :
    gameF q 5 = q + 4 := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
      apply gameF_value_of_source_mex (q := q) (r := 5) (m := q + 4) (by omega)
      · rintro ⟨h5q, hcarry⟩
        by_cases hq7 : q = 7
        · subst q
          rw [gameF_six_five] at hcarry
          omega
        · have hprev := ih (q - 1) (by omega) (by omega)
          rw [hprev] at hcarry
          omega
      · omega
      · rintro (⟨a, haq, hval⟩ | ⟨b, hb5, hval⟩)
        · by_cases ha7 : 7 ≤ a
          · have hmin : min a 5 = 5 := Nat.min_eq_right (by omega)
            rw [hmin, ih a haq ha7] at hval
            omega
          · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨
                a = 4 ∨ a = 5 ∨ a = 6 := by omega
            rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · simp [gameF_zero_zero] at hval <;> omega
            · simp [gameF_one_one] at hval <;> omega
            · simp [gameF_diag_two] at hval <;> omega
            · simp [gameF_diag_three] at hval <;> omega
            · simp [gameF_diag_four] at hval <;> omega
            · simp [gameF_diag_five] at hval <;> omega
            · simp [gameF_six_five] at hval <;> omega
        · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
          rcases hcase with rfl | rfl | rfl | rfl | rfl
          · rw [gameF_col0] at hval; omega
          · rw [gameF_col1_rail (q := q) (by omega)] at hval; omega
          · rw [gameF_col2_rail (q := q) (by omega)] at hval; omega
          · rw [gameF_col3_rail (q := q) (by omega)] at hval; omega
          · rw [gameF_col4_rail (q := q) (by omega)] at hval; omega
      · intro k hk0 hklt
        by_cases hk11 : k < 11
        · have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
              k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
          rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
          · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := q) (by omega)⟩
          · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
          · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
          · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := q) (by omega)⟩
          · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
          · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := q) (by omega)⟩
          · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
          · exact Or.inl ⟨6, by omega, gameF_six_five⟩
          · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
        · let a := k - 4
          have ha7 : 7 ≤ a := by dsimp [a]; omega
          have haq : a < q := by dsimp [a]; omega
          refine Or.inl ⟨a, haq, ?_⟩
          have hmin : min a 5 = 5 := Nat.min_eq_right (by omega)
          rw [hmin, ih a haq ha7]
          dsimp [a]
          omega

/-- `d(6)=11`. -/
theorem gameF_diag_six : gameF 6 6 = 11 := by
  apply gameF_value_of_source_mex (q := 6) (r := 6) (m := 11)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 6) (by omega)] at hval; omega
      · rw [gameF_six_four] at hval; omega
      · rw [gameF_six_five] at hval; omega
  · intro k hk0 hk11
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 6) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 6) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 6⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨5, by omega, gameF_six_five⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩

/-- First pre-freeze cell in column 6. -/
theorem gameF_seven_six : gameF 7 6 = 12 := by
  apply gameF_value_of_source_mex (q := 7) (r := 6) (m := 12)
  · omega
  · rw [gameF_diag_six]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 7) (by omega)] at hval; omega
  · intro k hk0 hk12
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 7) (by omega)⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 7⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩

/-- Second pre-freeze cell in column 6. -/
theorem gameF_eight_six : gameF 8 6 = 13 := by
  apply gameF_value_of_source_mex (q := 8) (r := 6) (m := 13)
  · omega
  · rw [gameF_seven_six]
    omega
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
      · simp [gameF_seven_six] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 8) (by omega)] at hval; omega
  · intro k hk0 hk13
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 8⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inl ⟨7, by omega, gameF_seven_six⟩

/-- The blocker freeze cell `F(9,6)=9`. -/
theorem gameF_nine_six : gameF 9 6 = 9 := by
  apply gameF_value_of_source_mex (q := 9) (r := 6) (m := 9)
  · omega
  · rw [gameF_eight_six]
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
      · simp [gameF_seven_six] at hval
      · simp [gameF_eight_six] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 9) (by omega)] at hval; omega
  · intro k hk0 hk9
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩

/-- Constant blocker rail: `F(q,6)=9` from its row-9 freeze onward. -/
theorem gameF_col6_rail {q : Nat} (hq : 9 ≤ q) : gameF q 6 = 9 := by
  have hsmall : gameF 9 6 < 9 + 1 := by rw [gameF_nine_six]; omega
  have hconst := constant_from gameRecurrenceModel
    (q := 9) (r := 6) (by omega) hsmall (q - 9)
  change gameF (9 + (q - 9)) 6 = gameF 9 6 at hconst
  have hsum : 9 + (q - 9) = q := by omega
  rw [hsum, gameF_nine_six] at hconst
  exact hconst

/-- No value above the blocker `9` can have its row-start freeze in column 6. -/
theorem gameF_no_high_rowstart_col6 {v : Nat} (hv : 10 ≤ v) :
    gameF v 6 ≠ v := by
  rw [gameF_col6_rail (q := v) (by omega)]
  omega

end ChompLean
