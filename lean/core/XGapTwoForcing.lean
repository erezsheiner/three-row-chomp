import R201DiagDoubleSlackCeilingChain
import R151FAtomicPreview
import R149dBackwardMexPrefixForcing
import R212B43BlockerRankSlackAudit
import EarlyCol13Col14Rails

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ChompLean

private theorem xgap2_nodup_map_of_injective_on
    (f : Nat -> Nat) (xs : List Nat)
    (hxs : xs.Nodup)
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
      f x = f y -> x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      change (f a :: as.map f).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hay⟩
        have hay' : a = y :=
          hinj a (by simp) y (by simp [hy]) hay.symm
        subst y
        exact hxs.1 hy
      · apply ih hxs.2
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

private theorem xgap2_nodup_get_injective
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {xs : List alpha} (hxs : xs.Nodup) :
    Function.Injective xs.get := by
  induction xs with
  | nil => intro i; exact Fin.elim0 i
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro _; rfl
        · intro hij
          exfalso
          have haj : a = as.get j' := by simpa using hij
          exact hxs.1 (by rw [haj]; exact List.get_mem as j')
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij
          exfalso
          have hia : as.get i' = a := by simpa using hij
          exact hxs.1 (by rw [← hia]; exact List.get_mem as i')
        · intro hij
          have htail : i' = j' := ih hxs.2 (by simpa using hij)
          exact Fin.ext (by simpa using congrArg Fin.val htail)

/-- A canonical freeze column for an actual blocker. -/
noncomputable def gameFGapTwoFreezeColumn (k : Nat) : Nat := by
  classical
  exact if h : S gameF k then Classical.choose h else 0

theorem gameFGapTwoFreezeColumn_spec {k : Nat}
    (hS : S gameF k) :
    gameFGapTwoFreezeColumn k < k ∧
      gameF k (gameFGapTwoFreezeColumn k) = k := by
  classical
  simp only [gameFGapTwoFreezeColumn, dif_pos hS]
  exact Classical.choose_spec hS

noncomputable def gameFGapTwoFreezeColsThroughList (n : Nat) : List Nat :=
  (gameFBlockersThroughList n).map gameFGapTwoFreezeColumn

theorem gameFGapTwoFreezeColsThroughList_length (n : Nat) :
    (gameFGapTwoFreezeColsThroughList n).length =
      gameFBlockerCountThrough n := by
  simp [gameFGapTwoFreezeColsThroughList, gameFBlockerCountThrough]

theorem gameFGapTwoFreezeColsThroughList_nodup (n : Nat) :
    (gameFGapTwoFreezeColsThroughList n).Nodup := by
  classical
  unfold gameFGapTwoFreezeColsThroughList
  apply xgap2_nodup_map_of_injective_on gameFGapTwoFreezeColumn
    (gameFBlockersThroughList n) (gameF_blockersThroughList_nodup n)
  intro x hx y hy hcol
  have hxS := (gameF_mem_blockersThroughList.mp hx).2.2
  have hyS := (gameF_mem_blockersThroughList.mp hy).2.2
  have hxspec := gameFGapTwoFreezeColumn_spec hxS
  have hyspec := gameFGapTwoFreezeColumn_spec hyS
  by_cases hxy : x = y
  · exact hxy
  · by_cases hlt : x < y
    · exact False.elim (gameF_freeze_column_unique
        hxspec.1 hxspec.2 hlt (by simpa [hcol] using hyspec.2))
    · have hyx : y < x := by omega
      exact False.elim (gameF_freeze_column_unique
        hyspec.1 hyspec.2 hyx (by simpa [hcol] using hxspec.2))

/-- Under a freeze no more than two rows to the right of its column, every
earlier blocker has its canonical freeze column strictly left of that
column. -/
theorem gameFGapTwoFreezeColsThroughList_subset_range
    {v c : Nat}
    (hcv : c < v) (hvc2 : v <= c + 2)
    (hstart : gameF v c = v) :
    gameFGapTwoFreezeColsThroughList (v - 1) ⊆ List.range c := by
  classical
  intro e he
  rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
  have hkdata := gameF_mem_blockersThroughList.mp hk
  have hkspec := gameFGapTwoFreezeColumn_spec hkdata.2.2
  have hkltv : k < v := by omega
  have hle : gameFGapTwoFreezeColumn k <= c := by omega
  have hne : gameFGapTwoFreezeColumn k ≠ c := by
    intro heq
    exact gameF_freeze_column_unique
      hkspec.1 hkspec.2 hkltv (by simpa [heq] using hstart)
  exact List.mem_range.mpr (by omega)

/-- Columns left of `c` not occupied by a canonical earlier freeze. -/
noncomputable def gameFGapTwoActiveCols (v c : Nat) : List Nat := by
  classical
  exact (List.range c).filter (fun e =>
    decide (e ∉ gameFGapTwoFreezeColsThroughList (v - 1)))

theorem gameFGapTwoActiveCols_nodup (v c : Nat) :
    (gameFGapTwoActiveCols v c).Nodup := by
  classical
  unfold gameFGapTwoActiveCols
  exact List.filter_sublist.nodup List.nodup_range

theorem gameF_mem_gapTwoActiveCols {v c e : Nat} :
    e ∈ gameFGapTwoActiveCols v c ↔
      e < c ∧ e ∉ gameFGapTwoFreezeColsThroughList (v - 1) := by
  classical
  simp [gameFGapTwoActiveCols]

/-- The early freeze columns and active columns partition `[0,c)`. -/
theorem gameFGapTwo_active_freeze_partition
    {v c : Nat}
    (hcv : c < v) (hvc2 : v <= c + 2)
    (hstart : gameF v c = v) :
    c = gameFBlockerCountThrough (v - 1) +
      (gameFGapTwoActiveCols v c).length := by
  classical
  let frozen := gameFGapTwoFreezeColsThroughList (v - 1)
  let frozenFilter := (List.range c).filter (fun e => decide (e ∈ frozen))
  let active := gameFGapTwoActiveCols v c
  have hfrozenNodup : frozen.Nodup := by
    exact gameFGapTwoFreezeColsThroughList_nodup (v - 1)
  have hfrozenSub : frozen ⊆ List.range c := by
    exact gameFGapTwoFreezeColsThroughList_subset_range hcv hvc2 hstart
  have hfilterNodup : frozenFilter.Nodup := by
    dsimp [frozenFilter]
    exact List.filter_sublist.nodup List.nodup_range
  have hfilterSubFrozen : frozenFilter ⊆ frozen := by
    intro e he
    have hdec := (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hdec
  have hfrozenSubFilter : frozen ⊆ frozenFilter := by
    intro e he
    apply List.mem_filter.mpr
    exact ⟨hfrozenSub he, by simp [he]⟩
  have hle₁ := nodup_subset_length_le hfilterNodup hfilterSubFrozen
  have hle₂ := nodup_subset_length_le hfrozenNodup hfrozenSubFilter
  have hfilterLen : frozenFilter.length = frozen.length := by omega
  have hraw := List.length_eq_countP_add_countP
    (fun e : Nat => decide (e ∈ frozen)) (l := List.range c)
  simp only [List.countP_eq_length_filter] at hraw
  have hpartition : c = frozenFilter.length + active.length := by
    simpa [frozenFilter, active, frozen, gameFGapTwoActiveCols] using hraw
  have hfrozenLen : frozen.length =
      gameFBlockerCountThrough (v - 1) := by
    exact gameFGapTwoFreezeColsThroughList_length (v - 1)
  calc
    c = frozenFilter.length + active.length := hpartition
    _ = frozen.length + active.length := by rw [hfilterLen]
    _ = gameFBlockerCountThrough (v - 1) +
        (gameFGapTwoActiveCols v c).length := by
          rw [hfrozenLen]

/-- Every active column left of a terminal freeze hosts the blocker earlier,
on a row whose diagonal lies strictly above the blocker.  This is the
formal T-A hosting step from the R02 certificate. -/
theorem gameFGapTwo_active_has_high_diagonal_host
    {v c e : Nat}
    (hcv : c < v) (hstart : gameF v c = v)
    (he : e ∈ gameFGapTwoActiveCols v c) :
    ∃ x, e < x ∧ x < v ∧ gameF x e = v ∧ v < gameF x x := by
  classical
  have hedata := gameF_mem_gapTwoActiveCols.mp he
  have hev : e <= v := by omega
  have hhigh : v < gameF v e := by
    apply Nat.lt_of_not_ge
    intro hnot
    have hlow : gameF v e <= v := hnot
    have hcell := gameF_low_cell_has_rowstart hev hlow
    let k := gameF v e
    have hek : e < k := by simpa [k] using hcell.1
    have hkstart : gameF k e = k := by simpa [k] using hcell.2
    by_cases hkv : k = v
    · have hec : e = c := by
        apply gameRecurrenceModel.fixed_q_injective
          (q := v) (b₁ := e) (b₂ := c) (by omega) (by omega)
        change gameF v e = gameF v c
        rw [hstart]
        simpa [k] using hkv
      omega
    · have hklt : k < v := by omega
      have hkpos : 0 < k := by omega
      have hkS : S gameF k := ⟨e, hek, hkstart⟩
      have hkMem : k ∈ gameFBlockersThroughList (v - 1) := by
        apply gameF_mem_blockersThroughList.mpr
        exact ⟨hkpos, by omega, hkS⟩
      have hfreezeMem : gameFGapTwoFreezeColumn k ∈
          gameFGapTwoFreezeColsThroughList (v - 1) := by
        apply List.mem_map.mpr
        exact ⟨k, hkMem, rfl⟩
      have hkspec := gameFGapTwoFreezeColumn_spec hkS
      have hcol : gameFGapTwoFreezeColumn k = e := by
        apply gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hkspec.1) (Nat.le_of_lt hek)
        exact hkspec.2.trans hkstart.symm
      exact hedata.2 (by simpa [hcol] using hfreezeMem)
  have hmex := recurrence_high_output_exact_mex gameF_brouwerRecurrence
    (q := v) (c := e) (v := gameF v e) hev hhigh rfl
  have hblocked : B gameF v e v := hmex.2.2 v (by omega) hhigh
  rcases hblocked with hR | hC
  · rcases hR with ⟨x, hxv, hx⟩
    by_cases hxe : x <= e
    · have hdiag : gameF x x = v := by
        simpa [Nat.min_eq_left hxe] using hx
      have hD : D gameF v := ⟨x, hdiag⟩
      have hS : S gameF v := ⟨c, hcv, hstart⟩
      exact False.elim (disjoint_D_S gameRecurrenceModel hD hS)
    · have hex : e < x := by omega
      have hhost : gameF x e = v := by
        simpa [Nat.min_eq_right (Nat.le_of_lt hex)] using hx
      have hrowMax := recurrence_strict_row_diagonal_maximal
        gameRecurrenceModel hex
      change gameF x e < gameF x x at hrowMax
      exact ⟨x, hex, hxv, hhost, by omega⟩
  · rcases hC with ⟨b, hbe, hb⟩
    have hbc : b = c := by
      exact gameRecurrenceModel.fixed_q_injective
        (q := v) (b₁ := b) (b₂ := c) (by omega) (by omega)
        (hb.trans hstart.symm)
    omega

/-- T-B: the active columns inject into high-diagonal rows.  Completing
those rows by the canonical diagonal owners of all nonblockers through `v`
packs both disjoint families into the `v` rows below `v`. -/
theorem gameFGapTwo_active_count_le_blockers
    {v c : Nat}
    (hcv : c < v) (hstart : gameF v c = v) :
    (gameFGapTwoActiveCols v c).length <=
      gameFBlockerCountThrough v := by
  classical
  let active := gameFGapTwoActiveCols v c
  let nonblockers := gameFNonblockersThroughList v
  have hactiveNodup : active.Nodup := by
    exact gameFGapTwoActiveCols_nodup v c
  have hhostExists : forall i : Fin active.length,
      exists x, active.get i < x ∧ x < v ∧
        gameF x (active.get i) = v ∧ v < gameF x x := by
    intro i
    apply gameFGapTwo_active_has_high_diagonal_host hcv hstart
    exact List.get_mem active i
  let hostNat : Fin active.length -> Nat := fun i =>
    Classical.choose (hhostExists i)
  have hhostSpec : forall i : Fin active.length,
      active.get i < hostNat i ∧ hostNat i < v ∧
        gameF (hostNat i) (active.get i) = v ∧
          v < gameF (hostNat i) (hostNat i) := by
    intro i
    exact Classical.choose_spec (hhostExists i)
  let host : Fin active.length -> Fin v := fun i =>
    ⟨hostNat i, (hhostSpec i).2.1⟩
  have hhostInj : Function.Injective host := by
    have hgetInj : Function.Injective (fun i : Fin active.length =>
        active.get i) := xgap2_nodup_get_injective hactiveNodup
    intro i j hij
    have hrow : hostNat i = hostNat j := congrArg Fin.val hij
    have hi := hhostSpec i
    have hj := hhostSpec j
    have hcols : active.get i = active.get j := by
      apply gameRecurrenceModel.fixed_q_injective
        (q := hostNat i) (b₁ := active.get i) (b₂ := active.get j)
        (by omega) (by omega)
      change gameF (hostNat i) (active.get i) =
        gameF (hostNat i) (active.get j)
      rw [hi.2.2.1]
      rw [hrow]
      exact hj.2.2.1.symm
    exact hgetInj hcols
  have hnonblockersNodup : nonblockers.Nodup := by
    dsimp [nonblockers, gameFNonblockersThroughList]
    exact List.filter_sublist.nodup (List.nodup_range' 1)
  have hownerData : forall i : Fin nonblockers.length,
      0 < nonblockers.get i ∧ nonblockers.get i <= v ∧
        Not (S gameF (nonblockers.get i)) := by
    intro i
    apply gameF_mem_nonblockersThroughList.mp
    exact List.get_mem nonblockers i
  have hownerSpec : forall i : Fin nonblockers.length,
      gameF (gameFDiagonalOwner (nonblockers.get i))
        (gameFDiagonalOwner (nonblockers.get i)) = nonblockers.get i := by
    intro i
    exact gameFDiagonalOwner_spec (hownerData i).1 (hownerData i).2.2
  have hownerLt : forall i : Fin nonblockers.length,
      gameFDiagonalOwner (nonblockers.get i) < v := by
    intro i
    have hgt := gameRecurrenceModel.diagonal_gt
      (gameFDiagonalOwner (nonblockers.get i))
    change gameFDiagonalOwner (nonblockers.get i) <
      gameF (gameFDiagonalOwner (nonblockers.get i))
        (gameFDiagonalOwner (nonblockers.get i)) at hgt
    rw [hownerSpec i] at hgt
    have hkle := (hownerData i).2.1
    omega
  let owner : Fin nonblockers.length -> Fin v := fun i =>
    ⟨gameFDiagonalOwner (nonblockers.get i), hownerLt i⟩
  have hownerInj : Function.Injective owner := by
    have hgetInj : Function.Injective (fun i : Fin nonblockers.length =>
        nonblockers.get i) := xgap2_nodup_get_injective hnonblockersNodup
    intro i j hij
    have hrow : gameFDiagonalOwner (nonblockers.get i) =
        gameFDiagonalOwner (nonblockers.get j) := congrArg Fin.val hij
    have hi := hownerSpec i
    have hj := hownerSpec j
    rw [hrow] at hi
    exact hgetInj (hi.symm.trans hj)
  have hcross : forall i j, host i ≠ owner j := by
    intro i j hij
    have hrow : hostNat i = gameFDiagonalOwner (nonblockers.get j) :=
      congrArg Fin.val hij
    have hhighDiag := (hhostSpec i).2.2.2
    have hown := hownerSpec j
    rw [hrow] at hhighDiag
    rw [hown] at hhighDiag
    have hjle := (hownerData j).2.1
    omega
  have hhall := r148b_two_packet_ordered_hall
    host owner hhostInj hownerInj hcross
  have hpartition0 := List.length_eq_countP_add_countP
    (fun k : Nat => decide (S gameF k)) (l := List.range' 1 v)
  simp only [List.countP_eq_length_filter] at hpartition0
  have hpartition : v = gameFBlockerCountThrough v + nonblockers.length := by
    simpa [gameFBlockerCountThrough, gameFBlockersThroughList,
      nonblockers, gameFNonblockersThroughList] using hpartition0
  have hle : active.length <= gameFBlockerCountThrough v := by omega
  simpa [active] using hle

/-- The exact lower count seam needed for gap two. -/
theorem gameF_gap_two_blocker_count_lower
    {c : Nat} (h : gameF (c + 2) c = c + 2) :
    c <= 2 * gameFBlockerCountThrough (c + 1) + 1 := by
  have hpartition := gameFGapTwo_active_freeze_partition
    (v := c + 2) (c := c) (by omega) (by omega) h
  have hactive := gameFGapTwo_active_count_le_blockers
    (v := c + 2) (c := c) (by omega) h
  have hS : S gameF (c + 2) := ⟨c, by omega, h⟩
  have hstep := gameFBlockerCountThrough_succ_of_blocker
    (n := c + 1) hS
  have hi1 : c + 2 - 1 = c + 1 := by omega
  have hi2 : c + 1 + 1 = c + 2 := by omega
  rw [hi1] at hpartition
  rw [hi2] at hstep
  omega

/-- Actual-game gap-two forcing: the unique possible column is `3`. -/
theorem gameF_gap_two_forcing
    {c : Nat} (h : gameF (c + 2) c = c + 2) :
    c = 3 := by
  by_cases hc : 15 <= c
  · have hlower := gameF_gap_two_blocker_count_lower h
    have hceiling := gameFBlockerCountThrough_ceiling
      (a := c + 1) (by omega)
    omega
  · have hc14 : c <= 14 := by omega
    have hcase : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨
        c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨
        c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hh : gameF 2 0 = 2 := by simpa using h
      rw [gameF_col0] at hh
      omega
    · have hh : gameF 3 1 = 3 := by simpa using h
      rw [gameF_col1_rail (q := 3) (by omega)] at hh
      omega
    · have hh : gameF 4 2 = 4 := by simpa using h
      rw [gameF_col2_rail (q := 4) (by omega)] at hh
      omega
    · rfl
    · have hh : gameF 6 4 = 6 := by simpa using h
      rw [gameF_six_four] at hh
      omega
    · have hh : gameF 7 5 = 7 := by simpa using h
      rw [gameF_col5_rail (q := 7) (by omega)] at hh
      omega
    · have hh : gameF 8 6 = 8 := by simpa using h
      rw [gameF_eight_six] at hh
      omega
    · have hh : gameF 9 7 = 9 := by simpa using h
      rw [gameF_nine_seven] at hh
      omega
    · have hh : gameF 10 8 = 10 := by simpa using h
      rw [gameF_ten_eight] at hh
      omega
    · have hh : gameF 11 9 = 11 := by simpa using h
      rw [gameF_eleven_nine] at hh
      omega
    · have hh : gameF 12 10 = 12 := by simpa using h
      rw [gameF_twelve_ten] at hh
      omega
    · have hh : gameF 13 11 = 13 := by simpa using h
      rw [gameF_thirteen_eleven] at hh
      omega
    · have hh : gameF 14 12 = 14 := by simpa using h
      rw [gameF_fourteen_twelve] at hh
      omega
    · have hh : gameF 15 13 = 15 := by simpa using h
      rw [gameF_fifteen_thirteen] at hh
      omega
    · have hh : gameF 16 14 = 16 := by simpa using h
      rw [gameF_sixteen_fourteen] at hh
      omega

#print axioms gameF_gap_two_blocker_count_lower
#print axioms gameF_gap_two_forcing

end ChompLean
