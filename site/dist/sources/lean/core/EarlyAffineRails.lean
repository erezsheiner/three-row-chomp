import GameFCol5Rail

set_option autoImplicit false

namespace ChompLean

/-!
# Early affine fixed-column rails

This file extends the exact low-column calculation beyond column five.  The
generic lemma below isolates the induction used repeatedly: a finite old-row
window and a permanent low-value cover start an affine tail, while the tail
itself supplies every later value in order.
-/

/-- A fixed column has an affine tail once its finite old-row window, the
current-row prefix, and the permanent low source cover are controlled. -/
theorem gameF_affine_fixed_column_of_source_frame
    {c t d : Nat}
    (hct : c <= t)
    (hd : 1 <= d)
    (hbaseNC : Not (c < t /\ gameF (t - 1) c < t))
    (hearly : forall a, a < t -> gameF a (min a c) < t + d)
    (hprefix : forall q, t <= q -> forall b, b < c -> gameF q b < q + d)
    (hlow : forall q, t <= q -> forall k,
      0 < k -> k < t + d -> B gameF q c k) :
    forall q, t <= q -> gameF q c = q + d := by
  intro q htq
  induction q using Nat.strongRecOn with
  | ind q ih =>
      apply gameF_value_of_source_mex (by omega)
      · rintro ⟨hcq, hcarry⟩
        by_cases hqt : q = t
        · subst q
          exact hbaseNC ⟨hcq, hcarry⟩
        · have htprev : t <= q - 1 := by omega
          have hiprev := ih (q - 1) (by omega) htprev
          rw [hiprev] at hcarry
          omega
      · omega
      · intro hsource
        rcases hsource with hR | hC
        · rcases hR with ⟨a, haq, hvalue⟩
          by_cases hat : a < t
          · have hsmall := hearly a hat
            rw [hvalue] at hsmall
            omega
          · have hta : t <= a := by omega
            have hca : c <= a := by omega
            have hia := ih a haq hta
            rw [Nat.min_eq_right hca, hia] at hvalue
            omega
        · rcases hC with ⟨b, hbc, hvalue⟩
          have hsmall := hprefix q htq b hbc
          rw [hvalue] at hsmall
          omega
      · intro k hkpos hklt
        by_cases hklow : k < t + d
        · exact hlow q htq k hkpos hklow
        · have hdk : d <= k := by omega
          have hta : t <= k - d := by omega
          have haq : k - d < q := by omega
          have hca : c <= k - d := by omega
          have hia := ih (k - d) haq hta
          refine Or.inl ⟨k - d, haq, ?_⟩
          rw [Nat.min_eq_right hca, hia]
          omega

/-! ## Column seven -/

/-- First diagonal needed by the column-seven start window. -/
theorem gameF_seven_seven : gameF 7 7 = 13 := by
  apply gameF_value_of_source_mex (q := 7) (r := 7) (m := 13)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/
          a = 4 \/ a = 5 \/ a = 6 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/
          b = 4 \/ b = 5 \/ b = 6 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 7) (by omega)] at hval; omega
      · rw [gameF_seven_six] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 := by
      omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 7) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨6, by omega, gameF_seven_six⟩

/-- The second old-row value in the column-seven start window. -/
theorem gameF_eight_seven : gameF 8 7 = 14 := by
  apply gameF_value_of_source_mex (q := 8) (r := 7) (m := 14)
  · omega
  · rw [gameF_seven_seven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/
          a = 4 \/ a = 5 \/ a = 6 \/ a = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
      · simp [gameF_seven_seven] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/
          b = 4 \/ b = 5 \/ b = 6 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_eight_six] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
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

/-- The final exceptional value before the column-seven affine tail. -/
theorem gameF_nine_seven : gameF 9 7 = 12 := by
  apply gameF_value_of_source_mex (q := 9) (r := 7) (m := 12)
  · omega
  · rw [gameF_eight_seven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/
          a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
      · simp [gameF_seven_seven] at hval
      · simp [gameF_eight_seven] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/
          b = 4 \/ b = 5 \/ b = 6 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_nine_six] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 := by
      omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
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

/-- Affine column-seven rail: `F(q,7)=q+5` from row ten onward. -/
theorem gameF_col7_rail {q : Nat} (hq : 10 <= q) : gameF q 7 = q + 5 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 7) (t := 10) (d := 5) (q := q) (by omega) (by omega)
  · rw [gameF_nine_seven]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
        a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [gameF_zero_zero]
    · simp [gameF_one_one]
    · simp [gameF_diag_two]
    · simp [gameF_diag_three]
    · simp [gameF_diag_four]
    · simp [gameF_diag_five]
    · simp [gameF_diag_six]
    · simp [gameF_seven_seven]
    · simp [gameF_eight_seven]
    · simp [gameF_nine_seven]
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/
        b = 4 \/ b = 5 \/ b = 6 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [gameF_col0]; omega
    · rw [gameF_col1_rail (q := row) (by omega)]; omega
    · rw [gameF_col2_rail (q := row) (by omega)]; omega
    · rw [gameF_col3_rail (q := row) (by omega)]; omega
    · rw [gameF_col4_rail (q := row) (by omega)]; omega
    · rw [gameF_col5_rail (q := row) (by omega)]; omega
    · rw [gameF_col6_rail (q := row) (by omega)]; omega
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨9, by omega, by simpa using gameF_nine_seven⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_eight_seven⟩
  · exact hq

/-! ## Immediate R151 burn-row consequences -/

/-- A terminal-burn equality and a second occurrence in the same row pin
the terminal column by fixed-row injectivity. -/
theorem gameF_terminal_burn_column_of_same_row_host
    {a r v c : Nat}
    (hrpos : 0 < r)
    (hra : r <= a)
    (hca : c <= a)
    (hburn : gameF a (r - 1) = v)
    (hhost : gameF a c = v) :
    r = c + 1 := by
  have heq : r - 1 = c :=
    gameRecurrenceModel.fixed_q_injective (by omega) hca
      (hburn.trans hhost.symm)
  omega

/-- Paired-rail collision: an affine host on the burn row pins the terminal
column, and a different fixed value in the next column contradicts the target
freeze there. -/
theorem gameF_terminal_burn_killed_by_next_column
    {a r v c w : Nat}
    (hrpos : 0 < r)
    (hra : r <= a)
    (hca : c <= a)
    (hburn : gameF a (r - 1) = v)
    (hhost : gameF a c = v)
    (hstart : gameF v r = v)
    (hnext : gameF v (c + 1) = w)
    (hvw : Not (v = w)) :
    False := by
  have hr : r = c + 1 :=
    gameF_terminal_burn_column_of_same_row_host
      (a := a) (r := r) (v := v) (c := c)
      hrpos hra hca hburn hhost
  subst r
  rw [hnext] at hstart
  exact hvw hstart.symm

/-- In the R151 notation `v=q+3`, a burn on row `a=q-2` has offset five.
The column-seven rail therefore pins the freeze column to `r=8`. -/
theorem gameF_q_sub_two_terminal_burn_pins_eight
    {q r : Nat}
    (hq : 12 <= q)
    (hra : r <= q - 2)
    (hburn : gameF (q - 2) (r - 1) = q + 3) :
    r = 8 := by
  have hrpos : 0 < r := by
    by_cases hr0 : r = 0
    · subst r
      rw [show 0 - 1 = 0 by omega, gameF_col0] at hburn
      omega
    · omega
  have hrow : 10 <= q - 2 := by omega
  have hrail := gameF_col7_rail (q := q - 2) hrow
  have hhost : gameF (q - 2) 7 = q + 3 := by
    rw [hrail]
    omega
  exact gameF_terminal_burn_column_of_same_row_host
    (a := q - 2) (r := r) (v := q + 3) (c := 7)
    hrpos hra (by omega) hburn hhost

/-- The usual midpoint lower bound and strict upper-rail failure already
exclude the `a=q-2` burn row once the column-seven rail is available. -/
theorem gameF_no_q_sub_two_terminal_burn_of_midpoint
    {q r g : Nat}
    (hq : 12 <= q)
    (hra : r <= q - 2)
    (hfailure : g + 1 < r)
    (hmid : q + 2 <= 2 * g)
    (hburn : gameF (q - 2) (r - 1) = q + 3) :
    False := by
  have hr : r = 8 :=
    gameF_q_sub_two_terminal_burn_pins_eight hq hra hburn
  omega

end ChompLean
