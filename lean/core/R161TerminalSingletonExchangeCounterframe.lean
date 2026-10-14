import R160LiveTerminalSourceInterfaceCounterframe
import R14FrontierLaw

set_option autoImplicit false

namespace ChompLean

/-!
# Exact singleton-exchange counterframe

This finite source frame strengthens the R160 separation at one terminal
edge.  The predecessor cell `(20,5)` is the genuine MEX 21, the next cell
`(20,6)` is the genuine MEX 20 and a target freeze, every positive value
below 20 is present in both sources, and 20 is deleted across the edge.
Nevertheless the target's unique old host is `(10,5)`, the terminal column
is live below 20, and the host is not lag three.

The frame is not a global recurrence table.  Its purpose is to show that
even the complete *local* singleton source exchange cannot prove the live
lag-three atom; a proof must use cross-row recurrence chronology.
-/

def r161TerminalExchangeFrame (q b : Nat) : Nat :=
  if q <= 5 ∧ b = q then q + 1
  else if q = 20 ∧ b <= 4 then b + 7
  else if q = 20 ∧ b = 5 then 21
  else if q = 20 ∧ b = 6 then 20
  else if b = 5 ∧ 6 <= q ∧ q <= 9 then q + 6
  else if q = 10 ∧ b = 5 then 20
  else if b = 5 ∧ 11 <= q ∧ q <= 14 then q + 5
  else if b = 6 ∧ 7 <= q ∧ q <= 10 then q + 9
  else if b = 6 ∧ 11 <= q ∧ q <= 14 then q + 1
  else 1000 * (q + 1) + b + 100

/-- Literal predecessor source: it contains `1,...,20` and omits 21. -/
theorem r161_old_source_exact :
    BValueList r161TerminalExchangeFrame 20 5 =
      [1, 2, 3, 4, 5, 6,
       12, 13, 14, 15, 20, 16, 17, 18, 19,
       16105, 17105, 18105, 19105, 20105,
       7, 8, 9, 10, 11] := by
  decide

/-- Literal freeze source: it contains `1,...,19`, omits 20, and has the
fresh predecessor output 21 as its extra row-prefix source. -/
theorem r161_new_source_exact :
    BValueList r161TerminalExchangeFrame 20 6 =
      [1, 2, 3, 4, 5, 6, 7106,
       16, 17, 18, 19, 12, 13, 14, 15,
       16106, 17106, 18106, 19106, 20106,
       7, 8, 9, 10, 11, 21] := by
  decide

theorem r161_old_cell_isMex :
    IsMex (B r161TerminalExchangeFrame 20 5) 21 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 21 ∈ BValueList r161TerminalExchangeFrame 20 5 :=
      mem_BValueList_iff.mpr hB
    rw [r161_old_source_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r161_old_source_exact]
    simp
    omega

theorem r161_new_cell_isMex :
    IsMex (B r161TerminalExchangeFrame 20 6) 20 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 20 ∈ BValueList r161TerminalExchangeFrame 20 6 :=
      mem_BValueList_iff.mpr hB
    rw [r161_new_source_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r161_new_source_exact]
    simp
    omega

/-- The old target occurs only through the strict same-column tail. -/
theorem r161_target_is_parkedOnly :
    ParkedOnly r161TerminalExchangeFrame 20 5 20 := by
  refine ⟨⟨10, by omega, by omega, by decide⟩, ?_, ?_⟩
  · rintro ⟨a, ha20, ha5, hvalue⟩
    have haCases :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
      omega
    rcases haCases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [r161TerminalExchangeFrame] at hvalue
  · rintro ⟨b, hb5, hvalue⟩
    have hbCases : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
      omega
    rcases hbCases with rfl | rfl | rfl | rfl | rfl <;>
      simp [r161TerminalExchangeFrame] at hvalue

/-- The terminal predecessor column stays strictly high, hence has no lower
freeze, on every row between its cutoff and the target. -/
theorem r161_terminal_column_strictly_live :
    forall z, 5 < z -> z < 20 ->
      z < r161TerminalExchangeFrame z 5 := by
  intro z hz5 hz20
  have hzNot20 : z ≠ 20 := by omega
  have hzNotSmall : Not (z <= 5) := by omega
  by_cases h69 : 6 <= z ∧ z <= 9
  · simp [r161TerminalExchangeFrame, hzNotSmall, hzNot20, h69]
  by_cases hz10 : z = 10
  · subst z
    decide
  by_cases h1114 : 11 <= z ∧ z <= 14
  · simp [r161TerminalExchangeFrame, hzNotSmall, hzNot20, h69,
      hz10, h1114]
  · simp [r161TerminalExchangeFrame, hzNotSmall, hzNot20, h69,
      hz10, h1114]
    omega

theorem r161_terminal_column_live :
    ColumnLiveBelowFor r161TerminalExchangeFrame 20 5 := by
  intro z hz5 hz20 hfreeze
  have hhigh := r161_terminal_column_strictly_live z hz5 hz20
  omega

/-- Full local singleton exchange, in the same shape as the terminal packet
used at a failed upper rail. -/
theorem r161_exact_terminal_singleton_source_exchange :
    IsMex (B r161TerminalExchangeFrame 20 5)
        (r161TerminalExchangeFrame 20 5) /\
      20 < r161TerminalExchangeFrame 20 5 /\
      ParkedOnly r161TerminalExchangeFrame 20 5 20 /\
      (forall k, 0 < k -> k < 20 ->
        B r161TerminalExchangeFrame 20 5 k /\
          B r161TerminalExchangeFrame 20 6 k) /\
      B r161TerminalExchangeFrame 20 5 20 /\
      Not (B r161TerminalExchangeFrame 20 6 20) := by
  have hold : r161TerminalExchangeFrame 20 5 = 21 := by decide
  refine ⟨by simpa [hold] using r161_old_cell_isMex,
    by rw [hold]; omega, r161_target_is_parkedOnly, ?_,
    r161_old_cell_isMex.2.2 20 (by omega) (by omega),
    r161_new_cell_isMex.2.1⟩
  intro k hkpos hk20
  exact ⟨r161_old_cell_isMex.2.2 k hkpos (by omega),
    r161_new_cell_isMex.2.2 k hkpos hk20⟩

/-- Yet the terminal target host is depth ten in a live column. -/
theorem r161_singleton_exchange_violates_live_lag3_geometry :
    r161TerminalExchangeFrame 20 6 = 20 /\
      r161TerminalExchangeFrame 10 5 = 20 /\
      ColumnLiveBelowFor r161TerminalExchangeFrame 20 5 /\
      10 + 3 ≠ 20 := by
  exact ⟨by decide, by decide, r161_terminal_column_live, by omega⟩

/-- The old host is also unique in the relevant strict column interval. -/
theorem r161_terminal_target_old_host_unique
    {a : Nat}
    (ha5 : 5 < a) (ha20 : a < 20)
    (hhost : r161TerminalExchangeFrame a 5 = 20) :
    a = 10 := by
  have haNot20 : a ≠ 20 := by omega
  have haNotSmall : Not (a <= 5) := by omega
  by_cases h69 : 6 <= a ∧ a <= 9
  · simp [r161TerminalExchangeFrame, haNotSmall, haNot20, h69] at hhost
    omega
  by_cases ha10 : a = 10
  · exact ha10
  by_cases h1114 : 11 <= a ∧ a <= 14
  · simp [r161TerminalExchangeFrame, haNotSmall, haNot20, h69,
      ha10, h1114] at hhost
    omega
  · simp [r161TerminalExchangeFrame, haNotSmall, haNot20, h69,
      ha10, h1114] at hhost

#print axioms r161_old_cell_isMex
#print axioms r161_new_cell_isMex
#print axioms r161_target_is_parkedOnly
#print axioms r161_exact_terminal_singleton_source_exchange
#print axioms r161_singleton_exchange_violates_live_lag3_geometry
#print axioms r161_terminal_target_old_host_unique

end ChompLean
