import R172TerminalOnlyBraidLastTwoRowsNormalForm
import R148bPersistentHostOrderedHall
import EarlyCol15ConstantRail

set_option autoImplicit false

namespace ChompLean

/-!
# Terminal relay Hall saturation with the fixed early rails removed

The raw row-start relay injects the active rows `r < t < v` into the
`r` prefix columns.  The early constant rails are genuine unavailable
seats for that injection.  This file packages the corresponding Hall
count once and then applies it to a failed terminal high braid.
-/

/-- Hall count for a terminal relay after adjoining any finite injective
packet of prefix columns which cannot host the terminal value on an active
row. -/
theorem gameF_terminal_relay_hall_with_forbidden_columns
    {v r n : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (forbidden : Fin n -> Fin r)
    (hforbiddenInj : Function.Injective forbidden)
    (hforbidden : forall t, r < t -> t < v -> forall j,
      gameF t (forbidden j).val ≠ v) :
    v - r - 1 + n <= r := by
  classical
  let activeRow : Fin (v - r - 1) -> Nat := fun i => r + 1 + i.val
  have hactive : forall i, r < activeRow i /\ activeRow i < v := by
    intro i
    have hi := i.isLt
    dsimp [activeRow]
    omega
  have hExists : forall i, exists c, c < r /\ gameF (activeRow i) c = v := by
    intro i
    have hi := hactive i
    exact rowStartPropagation gameRecurrenceModel hstart hrv hi.1 hi.2
  let host : Fin (v - r - 1) -> Fin r := fun i =>
    ⟨Classical.choose (hExists i), (Classical.choose_spec (hExists i)).1⟩
  have hhost : forall i, gameF (activeRow i) (host i).val = v := by
    intro i
    exact (Classical.choose_spec (hExists i)).2
  have hhostInj : Function.Injective host := by
    intro i j hij
    apply Fin.ext
    have hi := hactive i
    have hj := hactive j
    have hcol : (host i).val = (host j).val := congrArg Fin.val hij
    by_cases hijOrder : i.val < j.val
    · have hrows : activeRow i < activeRow j := by
        dsimp [activeRow]
        omega
      exact False.elim (encoding_same_lower_no_repeat game_encodes
        (s := (host i).val) (t₁ := activeRow i) (t₂ := activeRow j) (p := v)
        (by have := (host i).isLt; omega) hrows hj.2
        (hhost i) (by simpa [hcol] using hhost j))
    · by_cases hjiOrder : j.val < i.val
      · have hrows : activeRow j < activeRow i := by
          dsimp [activeRow]
          omega
        exact False.elim (encoding_same_lower_no_repeat game_encodes
          (s := (host j).val) (t₁ := activeRow j) (t₂ := activeRow i) (p := v)
          (by have := (host j).isLt; omega) hrows hi.2
          (hhost j) (by simpa [hcol] using hhost i))
      · omega
  have hcross : forall i j, host i ≠ forbidden j := by
    intro i j hij
    have hi := hactive i
    apply hforbidden (activeRow i) hi.1 hi.2 j
    have hval : (host i).val = (forbidden j).val := congrArg Fin.val hij
    simpa [hval] using hhost i
  exact r148b_two_packet_ordered_hall
    host forbidden hhostInj hforbiddenInj hcross

private theorem r175_active_col1_ne
    {v r t : Nat} (hr : 2 <= r) (hrt : r < t) (htv : t < v) :
    gameF t 1 ≠ v := by
  rw [gameF_col1_rail (q := t) (by omega)]
  omega

private theorem r175_active_col3_ne
    {v r t : Nat} (hr : 4 <= r) (hrt : r < t) (htv : t < v) :
    gameF t 3 ≠ v := by
  rw [gameF_col3_rail (q := t) (by omega)]
  omega

private theorem r175_active_col4_ne
    {v r t : Nat} (hr : 6 <= r) (hrt : r < t) (htv : t < v) :
    gameF t 4 ≠ v := by
  rw [gameF_col4_rail (q := t) (by omega)]
  omega

private theorem r175_active_col6_ne
    {v r t : Nat} (hr : 8 <= r) (hrt : r < t) (htv : t < v) :
    gameF t 6 ≠ v := by
  rw [gameF_col6_rail (q := t) (by omega)]
  omega

private theorem r175_active_col8_ne
    {v r t : Nat} (hr : 11 <= r) (hrt : r < t) (htv : t < v) :
    gameF t 8 ≠ v := by
  rw [gameF_col8_rail (q := t) (by omega)]
  omega

private theorem r175_active_col10_ne
    {v r t : Nat} (hr : 13 <= r) (hrt : r < t) (htv : t < v) :
    gameF t 10 ≠ v := by
  rw [gameF_col10_rail (q := t) (by omega)]
  omega

private theorem r175_active_col12_ne
    {v r t : Nat} (hr : 16 <= r) (hrt : r < t) (htv : t < v) :
    gameF t 12 ≠ v := by
  rw [gameF_col12_rail (q := t) (by omega)]
  omega

/-- The seven fixed prefix rails available once `r >= 16`. -/
private def r175ForbiddenRailValue (j : Fin 7) : Nat :=
  if j.val = 0 then 1 else if j.val = 1 then 3 else 2 * j.val

private theorem r175_forbiddenRailValue_le12 (j : Fin 7) :
    r175ForbiddenRailValue j <= 12 := by
  have hj := j.isLt
  by_cases hj0 : j.val = 0
  · simp [r175ForbiddenRailValue, hj0]
  · by_cases hj1 : j.val = 1
    · simp [r175ForbiddenRailValue, hj0, hj1]
    · simp [r175ForbiddenRailValue, hj0, hj1]
      omega

private theorem r175_forbiddenRailValue_injective :
    Function.Injective r175ForbiddenRailValue := by
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi0 : i.val = 0
  · by_cases hj0 : j.val = 0
    · omega
    · by_cases hj1 : j.val = 1
      · simp [r175ForbiddenRailValue, hi0, hj0, hj1] at hij
      · simp [r175ForbiddenRailValue, hi0, hj0, hj1] at hij
        omega
  · by_cases hi1 : i.val = 1
    · by_cases hj0 : j.val = 0
      · simp [r175ForbiddenRailValue, hi0, hi1, hj0] at hij
      · by_cases hj1 : j.val = 1
        · omega
        · simp [r175ForbiddenRailValue, hi0, hi1, hj0, hj1] at hij
          omega
    · by_cases hj0 : j.val = 0
      · simp [r175ForbiddenRailValue, hi0, hi1, hj0] at hij
        omega
      · by_cases hj1 : j.val = 1
        · simp [r175ForbiddenRailValue, hi0, hi1, hj0, hj1] at hij
          omega
        · simp [r175ForbiddenRailValue, hi0, hi1, hj0, hj1] at hij
          omega

private theorem r175_forbiddenRailValue_cases (j : Fin 7) :
    r175ForbiddenRailValue j = 1 ∨
    r175ForbiddenRailValue j = 3 ∨
    r175ForbiddenRailValue j = 4 ∨
    r175ForbiddenRailValue j = 6 ∨
    r175ForbiddenRailValue j = 8 ∨
    r175ForbiddenRailValue j = 10 ∨
    r175ForbiddenRailValue j = 12 := by
  have hj := j.isLt
  by_cases hj0 : j.val = 0
  · left
    simp [r175ForbiddenRailValue, hj0]
  · by_cases hj1 : j.val = 1
    · right; left
      simp [r175ForbiddenRailValue, hj0, hj1]
    · have hjcases :
          j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
          j.val = 5 ∨ j.val = 6 := by
        omega
      rcases hjcases with h | h | h | h | h
      · right; right; left
        simp [r175ForbiddenRailValue, hj0, hj1, h]
      · right; right; right; left
        simp [r175ForbiddenRailValue, hj0, hj1, h]
      · right; right; right; right; left
        simp [r175ForbiddenRailValue, hj0, hj1, h]
      · right; right; right; right; right; left
        simp [r175ForbiddenRailValue, hj0, hj1, h]
      · right; right; right; right; right; right
        simp [r175ForbiddenRailValue, hj0, hj1, h]

/-- Column `1` is never an active relay host.  Hence every terminal freeze
with `r >= 2` satisfies the first strict Hall bound `v <= 2*r`. -/
theorem gameF_terminal_relay_col1_strict_capacity
    {v r : Nat} (hrv : r < v) (hstart : gameF v r = v) (hr : 2 <= r) :
    v <= r + r := by
  let forbidden : Fin 1 -> Fin r := fun _ => ⟨1, by omega⟩
  have hinj : Function.Injective forbidden := by
    intro i j _
    exact Fin.ext (by omega)
  have hHall := gameF_terminal_relay_hall_with_forbidden_columns
    hrv hstart forbidden hinj (by
      intro t hrt htv _
      exact r175_active_col1_ne hr hrt htv)
  omega

/-- Once `r >= 4`, the constant columns `1` and `3` are both unavailable,
so the terminal value is one below the even Hall face. -/
theorem gameF_terminal_relay_col1_col3_capacity
    {v r : Nat} (hrv : r < v) (hstart : gameF v r = v) (hr : 4 <= r) :
    v <= r + r - 1 := by
  let forbidden : Fin 2 -> Fin r := fun j => ⟨2 * j.val + 1, by
    have := j.isLt
    omega⟩
  have hinj : Function.Injective forbidden := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp [forbidden] at hval
    omega
  have hHall := gameF_terminal_relay_hall_with_forbidden_columns
    hrv hstart forbidden hinj (by
      intro t hrt htv j
      have hj := j.isLt
      by_cases hj0 : j.val = 0
      · have hcol : (forbidden j).val = 1 := by
          dsimp [forbidden]
          omega
        simpa [hcol] using r175_active_col1_ne (by omega : 2 <= r) hrt htv
      · have hj1 : j.val = 1 := by omega
        have hcol : (forbidden j).val = 3 := by
          dsimp [forbidden]
          omega
        simpa [hcol] using r175_active_col3_ne hr hrt htv)
  omega

/-- Every failed deep terminal high braid already misses two Hall seats.
This is unconditional on the unresolved braid-order atom. -/
theorem gameF_failedTerminalHighBraid_two_rail_capacity
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a) :
    v <= r + r - 1 := by
  have hr2 : 2 <= r := by
    have := hbraid.failure
    omega
  have hfirst := gameF_terminal_relay_col1_strict_capacity
    hbraid.terminal.1 hbraid.terminal.2 hr2
  have hr4 : 4 <= r := by
    have := hbraid.targetLarge
    omega
  exact gameF_terminal_relay_col1_col3_capacity
    hbraid.terminal.1 hbraid.terminal.2 hr4

/-- The exact early rails rule out every freeze column below `16` for a
deep terminal high braid.  Constant terminal rails leave only five possible
freeze values (`12,14,17,19,22`); in each such case the old host on the
predecessor column is contradicted by the corresponding finite rail cell. -/
theorem gameF_failedTerminalHighBraid_freezeColumn_ge16
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a) :
    16 <= r := by
  have hstart := hbraid.terminal.2
  have hra := hbraid.oldHostChronology.1
  have hadeep := hbraid.oldHostChronology.2
  have hold := hbraid.oldHost
  have hcap := gameF_failedTerminalHighBraid_two_rail_capacity hbraid
  apply Nat.le_of_not_gt
  intro hr16
  have hrcases :
      r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨
      r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨
      r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
    omega
  rcases hrcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [gameF_col0] at hstart
    omega
  · rw [gameF_col1_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col2_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col3_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col4_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col5_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col6_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col7_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col8_rail (q := v) (by omega)] at hstart
    have hv : v = 12 := by omega
    subst v
    have ha : a = 8 := by omega
    subst a
    rw [gameF_eight_seven] at hold
    omega
  · rw [gameF_col9_rail (q := v) (by omega)] at hstart
    omega
  · rw [gameF_col10_rail (q := v) (by omega)] at hstart
    have hv : v = 14 := by omega
    subst v
    have ha : a = 10 := by omega
    subst a
    rw [gameF_ten_nine] at hold
    omega
  · have hvcases :
        v = 15 ∨ v = 16 ∨ v = 17 ∨ v = 18 ∨
        v = 19 ∨ v = 20 ∨ v = 21 := by
      omega
    rcases hvcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [gameF_fifteen_eleven] at hstart
      omega
    · rw [gameF_sixteen_eleven] at hstart
      omega
    · rw [gameF_seventeen_eleven] at hstart
      omega
    · rw [gameF_eighteen_eleven] at hstart
      omega
    · rw [gameF_col11_rail (q := 19) (by omega)] at hstart
      omega
    · rw [gameF_col11_rail (q := 20) (by omega)] at hstart
      omega
    · rw [gameF_col11_rail (q := 21) (by omega)] at hstart
      omega
  · by_cases hv17 : 17 <= v
    · rw [gameF_col12_rail (q := v) hv17] at hstart
      have hv : v = 17 := by omega
      subst v
      have hacases : a = 12 ∨ a = 13 := by omega
      rcases hacases with rfl | rfl
      · rw [gameF_twelve_eleven] at hold
        omega
      · rw [gameF_thirteen_eleven] at hold
        omega
    · have hv : v = 16 := by omega
      rw [hv, gameF_sixteen_twelve] at hstart
      omega
  · by_cases hv19 : 19 <= v
    · rw [gameF_col13_rail (q := v) hv19] at hstart
      have hv : v = 19 := by omega
      subst v
      have hacases : a = 13 ∨ a = 14 ∨ a = 15 := by omega
      rcases hacases with rfl | rfl | rfl
      · rw [gameF_thirteen_twelve] at hold
        omega
      · rw [gameF_fourteen_twelve] at hold
        omega
      · rw [gameF_fifteen_twelve] at hold
        omega
    · have hvcases : v = 17 ∨ v = 18 := by omega
      rcases hvcases with rfl | rfl
      · rw [gameF_seventeen_thirteen] at hstart
        omega
      · rw [gameF_eighteen_thirteen] at hstart
        omega
  · by_cases hv20 : 20 <= v
    · rw [gameF_col14_rail (q := v) hv20] at hstart
      omega
    · have hvcases : v = 18 ∨ v = 19 := by omega
      rcases hvcases with rfl | rfl
      · rw [gameF_eighteen_fourteen] at hstart
        omega
      · rw [gameF_nineteen_fourteen] at hstart
        omega
  · by_cases hv22 : 22 <= v
    · rw [gameF_col15_rail (q := v) hv22] at hstart
      have hv : v = 22 := by omega
      subst v
      have hacases : a = 15 ∨ a = 16 ∨ a = 17 ∨ a = 18 := by omega
      rcases hacases with rfl | rfl | rfl | rfl
      · rw [gameF_fifteen_fourteen] at hold
        omega
      · rw [gameF_sixteen_fourteen] at hold
        omega
      · rw [gameF_seventeen_fourteen] at hold
        omega
      · rw [gameF_eighteen_fourteen] at hold
        omega
    · have hvcases : v = 19 ∨ v = 20 ∨ v = 21 := by omega
      rcases hvcases with rfl | rfl | rfl
      · rw [gameF_nineteen_fifteen] at hstart
        omega
      · rw [gameF_twenty_fifteen] at hstart
        omega
      · rw [gameF_twentyone_fifteen] at hstart
        omega

/-- At a freeze column at least `16`, the seven constant rails
`1,3,4,6,8,10,12` are pairwise distinct unavailable Hall seats. -/
theorem gameF_terminal_relay_seven_fixed_rails_capacity
    {v r : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hr16 : 16 <= r) :
    v <= r + r - 6 := by
  let forbidden : Fin 7 -> Fin r := fun j =>
    ⟨r175ForbiddenRailValue j, by
      have hle := r175_forbiddenRailValue_le12 j
      omega⟩
  have hinj : Function.Injective forbidden := by
    intro i j hij
    apply r175_forbiddenRailValue_injective
    exact congrArg Fin.val hij
  have hHall := gameF_terminal_relay_hall_with_forbidden_columns
    hrv hstart forbidden hinj (by
      intro t hrt htv j
      change gameF t (r175ForbiddenRailValue j) ≠ v
      rcases r175_forbiddenRailValue_cases j with
          h | h | h | h | h | h | h
      · rw [h]
        exact r175_active_col1_ne (by omega : 2 <= r) hrt htv
      · rw [h]
        exact r175_active_col3_ne (by omega : 4 <= r) hrt htv
      · rw [h]
        exact r175_active_col4_ne (by omega : 6 <= r) hrt htv
      · rw [h]
        exact r175_active_col6_ne (by omega : 8 <= r) hrt htv
      · rw [h]
        exact r175_active_col8_ne (by omega : 11 <= r) hrt htv
      · rw [h]
        exact r175_active_col10_ne (by omega : 13 <= r) hrt htv
      · rw [h]
        exact r175_active_col12_ne hr16 hrt htv)
  omega

/-- Main braid corollary: the deep terminal packet forces `r >= 16` and
misses seven prefix seats, improving the raw `v <= 2*r+1` relay bound by
seven full units. -/
theorem gameF_failedTerminalHighBraid_seven_rail_capacity
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a) :
    v <= r + r - 6 := by
  exact gameF_terminal_relay_seven_fixed_rails_capacity
    hbraid.terminal.1 hbraid.terminal.2
    (gameF_failedTerminalHighBraid_freezeColumn_ge16 hbraid)

#print axioms gameF_terminal_relay_hall_with_forbidden_columns
#print axioms gameF_failedTerminalHighBraid_freezeColumn_ge16
#print axioms gameF_failedTerminalHighBraid_seven_rail_capacity

end ChompLean
