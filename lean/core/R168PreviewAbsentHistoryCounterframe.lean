import R168DeepTerminalLeftRelayNormalForm
import R161TerminalSingletonExchangeCounterframe

set_option autoImplicit false

namespace ChompLean

/-!
# Preview-absent terminal-history local counterframe

This finite source frame sharpens the R161 separation.  Across the terminal
edge `(20,5) -> (20,6)` the predecessor source has MEX 21 and the terminal
source has MEX 20.  The preview value `q=17` is absent from both exact column
histories, while the target 20 still has an old host at `(10,5)` below row 17.

Thus exact singleton exchange, live-column geometry, and preview absence do
not by themselves eliminate the old-history arm of causal depth.  This is a
local source frame, not a second global recurrence table.
-/

def r168PreviewAbsentFrame (q b : Nat) : Nat :=
  if q <= 5 ∧ b = q then q + 1
  else if q = 20 ∧ b <= 3 then b + 7
  else if q = 20 ∧ b = 4 then 17
  else if q = 20 ∧ b = 5 then 21
  else if q = 20 ∧ b = 6 then 20
  else if b = 5 ∧ 6 <= q ∧ q <= 9 then q + 5
  else if q = 10 ∧ b = 5 then 20
  else if b = 5 ∧ 11 <= q ∧ q <= 12 then q + 4
  else if b = 5 ∧ 13 <= q ∧ q <= 14 then q + 5
  else if b = 6 ∧ 7 <= q ∧ q <= 12 then q + 4
  else if b = 6 ∧ 13 <= q ∧ q <= 14 then q + 5
  else 1000 * (q + 1) + b + 100

/-- The predecessor source contains exactly the low values `1,...,20` and
omits 21. -/
theorem r168_previewAbsent_old_source_exact :
    BValueList r168PreviewAbsentFrame 20 5 =
      [1, 2, 3, 4, 5, 6,
       11, 12, 13, 14, 20, 15, 16, 18, 19,
       16105, 17105, 18105, 19105, 20105,
       7, 8, 9, 10, 17] := by
  decide

/-- The terminal source contains `1,...,19`, omits 20, and contains the old
cell output 21. -/
theorem r168_previewAbsent_new_source_exact :
    BValueList r168PreviewAbsentFrame 20 6 =
      [1, 2, 3, 4, 5, 6, 7106,
       11, 12, 13, 14, 15, 16, 18, 19,
       16106, 17106, 18106, 19106, 20106,
       7, 8, 9, 10, 17, 21] := by
  decide

theorem r168_previewAbsent_old_cell_isMex :
    IsMex (B r168PreviewAbsentFrame 20 5) 21 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 21 ∈ BValueList r168PreviewAbsentFrame 20 5 :=
      mem_BValueList_iff.mpr hB
    rw [r168_previewAbsent_old_source_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r168_previewAbsent_old_source_exact]
    simp
    omega

theorem r168_previewAbsent_new_cell_isMex :
    IsMex (B r168PreviewAbsentFrame 20 6) 20 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 20 ∈ BValueList r168PreviewAbsentFrame 20 6 :=
      mem_BValueList_iff.mpr hB
    rw [r168_previewAbsent_new_source_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r168_previewAbsent_new_source_exact]
    simp
    omega

/-- The preview value 17 is absent from the predecessor column history. -/
theorem r168_preview_absent_old_history :
    Not (ColHistPred r168PreviewAbsentFrame 20 5 17) := by
  rintro ⟨a, ha5, ha20, hvalue⟩
  have haNot20 : a ≠ 20 := by omega
  by_cases haSmall : a <= 5
  · have ha : a = 5 := by omega
    subst a
    simp [r168PreviewAbsentFrame] at hvalue
  by_cases h69 : 6 <= a ∧ a <= 9
  · simp [r168PreviewAbsentFrame, haSmall, haNot20, h69] at hvalue
    omega
  by_cases ha10 : a = 10
  · subst a
    simp [r168PreviewAbsentFrame] at hvalue
  by_cases h1112 : 11 <= a ∧ a <= 12
  · simp [r168PreviewAbsentFrame, haSmall, haNot20, h69, ha10,
      h1112] at hvalue
    omega
  by_cases h1314 : 13 <= a ∧ a <= 14
  · simp [r168PreviewAbsentFrame, haSmall, haNot20, h69, ha10,
      h1112, h1314] at hvalue
    omega
  · simp [r168PreviewAbsentFrame, haSmall, haNot20, h69, ha10,
      h1112, h1314] at hvalue

/-- The preview value 17 is also absent from the terminal column history. -/
theorem r168_preview_absent_new_history :
    Not (ColHistPred r168PreviewAbsentFrame 20 6 17) := by
  rintro ⟨a, ha6, ha20, hvalue⟩
  have haNotSmall : Not (a <= 5) := by omega
  have haNot20 : a ≠ 20 := by omega
  by_cases h712 : 7 <= a ∧ a <= 12
  · simp [r168PreviewAbsentFrame, haNotSmall, haNot20, h712] at hvalue
    omega
  by_cases h1314 : 13 <= a ∧ a <= 14
  · simp [r168PreviewAbsentFrame, haNotSmall, haNot20, h712,
      h1314] at hvalue
    omega
  · simp [r168PreviewAbsentFrame, haNotSmall, haNot20, h712,
      h1314] at hvalue

/-- The target still lies in the old history below the preview row. -/
theorem r168_old_target_history_survives :
    ColHistPred r168PreviewAbsentFrame 17 5 20 := by
  exact ⟨10, by omega, by omega, by decide⟩

theorem r168_previewAbsent_terminal_column_strictly_live :
    forall z, 5 < z -> z < 20 ->
      z < r168PreviewAbsentFrame z 5 := by
  intro z hz5 hz20
  have hzNotSmall : Not (z <= 5) := by omega
  have hzNot20 : z ≠ 20 := by omega
  by_cases h69 : 6 <= z ∧ z <= 9
  · simp [r168PreviewAbsentFrame, hzNotSmall, hzNot20, h69]
  by_cases hz10 : z = 10
  · subst z
    decide
  by_cases h1112 : 11 <= z ∧ z <= 12
  · simp [r168PreviewAbsentFrame, hzNotSmall, hzNot20, h69,
      hz10, h1112]
  by_cases h1314 : 13 <= z ∧ z <= 14
  · simp [r168PreviewAbsentFrame, hzNotSmall, hzNot20, h69,
      hz10, h1112, h1314]
  · simp [r168PreviewAbsentFrame, hzNotSmall, hzNot20, h69,
      hz10, h1112, h1314]
    omega

theorem r168_previewAbsent_terminal_column_live :
    ColumnLiveBelowFor r168PreviewAbsentFrame 20 5 := by
  intro z hz5 hz20 hfreeze
  have hhigh := r168_previewAbsent_terminal_column_strictly_live z hz5 hz20
  omega

/-- Complete separation packet: exact singleton exchange, liveness, and
preview absence coexist with a genuinely old target history and a depth-ten
host. -/
theorem r168_preview_absent_history_local_interface_counterframe :
    IsMex (B r168PreviewAbsentFrame 20 5)
        (r168PreviewAbsentFrame 20 5) ∧
      IsMex (B r168PreviewAbsentFrame 20 6)
        (r168PreviewAbsentFrame 20 6) ∧
      r168PreviewAbsentFrame 20 6 = 20 ∧
      r168PreviewAbsentFrame 10 5 = 20 ∧
      ColumnLiveBelowFor r168PreviewAbsentFrame 20 5 ∧
      Not (ColHistPred r168PreviewAbsentFrame 20 5 17) ∧
      Not (ColHistPred r168PreviewAbsentFrame 20 6 17) ∧
      ColHistPred r168PreviewAbsentFrame 17 5 20 ∧
      10 + 3 ≠ 20 := by
  have hold : r168PreviewAbsentFrame 20 5 = 21 := by decide
  have hnew : r168PreviewAbsentFrame 20 6 = 20 := by decide
  exact ⟨by simpa [hold] using r168_previewAbsent_old_cell_isMex,
    by simpa [hnew] using r168_previewAbsent_new_cell_isMex,
    hnew, by decide, r168_previewAbsent_terminal_column_live,
    r168_preview_absent_old_history, r168_preview_absent_new_history,
    r168_old_target_history_survives, by omega⟩

#print axioms r168_previewAbsent_old_cell_isMex
#print axioms r168_previewAbsent_new_cell_isMex
#print axioms r168_preview_absent_history_local_interface_counterframe

end ChompLean
