import R186Lag8LowerOwnerChannelClassification

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight greedy collapse after the seven occupied band values

On the row `t = q-5`, the six unconditional affine rails occupy

`t+1, t+2, t+4, t+5, t+6, t+7`,

and the W4 lower host occupies `t+3 = q-2`.  Hence a live column strictly
between that lower host and the high target, if it has no old target tail,
cannot emit an arbitrary low value.  The exact greedy ledger puts its output
in `[t,t+8)`, and row injectivity leaves only `t` itself.  Thus there is at
most one such clean live intermediate column; every other intermediate
column is an old carry or a literal old relay column of the target.
-/

/-- The lag-three host `q-2` on row `q-5` lies to the right of all six
affine rails used in the seven-value band argument. -/
theorem gameF_lag8_lowerHost_column_gt_eleven
    {q d : Nat}
    (hq : 26 <= q)
    (hdt : d <= q - 5)
    (hlower : gameF (q - 5) d = q - 2) :
    11 < d := by
  apply Nat.lt_of_not_ge
  intro hd
  have hcases :
      d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/
      d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · rw [gameF_col0] at hlower
    omega
  · rw [gameF_col1_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col2_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col3_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col4_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col5_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col6_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col7_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col8_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col9_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col10_rail (q := q - 5) (by omega)] at hlower
    omega
  · rw [gameF_col11_rail (q := q - 5) (by omega)] at hlower
    omega

/-- Exact seven-value collapse.  A non-carry intermediate column with no
old same-column copy of the terminal target must be the current row's own
freeze cell. -/
theorem gameF_lag8_between_hosts_live_nonTail_is_currentFreeze
    {q r g d e : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hdt : d <= q - 5)
    (hlower : gameF (q - 5) d = q - 2)
    (hde : d < e)
    (hec : e < r - 1)
    (hnotCarry :
      Not (e < q - 5 /\ gameF ((q - 5) - 1) e < q - 5))
    (hnoTail : Not (ColTail gameF (q - 5) e (q + 3))) :
    gameF (q - 5) e = q - 5 := by
  have hct : r - 1 <= q - 5 := by omega
  have hgt : g < q - 5 := by omega
  have hRclean : Not (R gameF (q - 5) e (q + 3)) := by
    intro hR
    exact hnoTail ((gameF_rowstart_R_iff_colTail hrv hstart).mp hR)
  have hband :=
    gameF_clean_noncarry_before_target_outputBand_and_ownerWindow
      howners hgt hct (by omega) hburn hec hnotCarry hRclean
  have houtLower : q - 5 <= gameF (q - 5) e := hband.1
  have houtUpper : gameF (q - 5) e < q + 3 := hband.2.1
  clear hband
  have hd11 : 11 < d :=
    gameF_lag8_lowerHost_column_gt_eleven hq hdt hlower
  have heRow : e <= q - 5 := by omega
  apply Classical.byContradiction
  intro hout
  have hcases :
      gameF (q - 5) e = (q - 5) + 1 \/
      gameF (q - 5) e = (q - 5) + 2 \/
      gameF (q - 5) e = (q - 5) + 3 \/
      gameF (q - 5) e = (q - 5) + 4 \/
      gameF (q - 5) e = (q - 5) + 5 \/
      gameF (q - 5) e = (q - 5) + 6 \/
      gameF (q - 5) e = (q - 5) + 7 := by
    omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have he0 : e = 0 :=
      gameRecurrenceModel.fixed_q_injective heRow (by omega)
        (h1.trans (gameF_col0 (q - 5)).symm)
    omega
  · have he2 : e = 2 :=
      gameRecurrenceModel.fixed_q_injective heRow (by omega)
        (h2.trans (gameF_col2_rail (q := q - 5) (by omega)).symm)
    omega
  · have hed : e = d :=
      gameRecurrenceModel.fixed_q_injective heRow hdt (by
        change gameF (q - 5) e = gameF (q - 5) d
        have hnum : q - 5 + 3 = q - 2 := by omega
        exact h3.trans (hnum.trans hlower.symm))
    omega
  · have he5 : e = 5 :=
      gameRecurrenceModel.fixed_q_injective heRow (by omega)
        (h4.trans (gameF_col5_rail (q := q - 5) (by omega)).symm)
    omega
  · have he7 : e = 7 :=
      gameRecurrenceModel.fixed_q_injective heRow (by omega)
        (h5.trans (gameF_col7_rail (q := q - 5) (by omega)).symm)
    omega
  · have he9 : e = 9 :=
      gameRecurrenceModel.fixed_q_injective heRow (by omega)
        (h6.trans (gameF_col9_rail (q := q - 5) (by omega)).symm)
    omega
  · have he11 : e = 11 :=
      gameRecurrenceModel.fixed_q_injective heRow (by omega)
        (h7.trans (gameF_col11_rail (q := q - 5) (by omega)).symm)
    omega

/-- There cannot be two distinct live, target-tail-clean columns strictly
between the W4 lower host and the lag-eight target host. -/
theorem gameF_lag8_between_hosts_atMostOne_live_nonTail
    {q r g d e1 e2 : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hdt : d <= q - 5)
    (hlower : gameF (q - 5) d = q - 2)
    (hde1 : d < e1) (he1c : e1 < r - 1)
    (hde2 : d < e2) (he2c : e2 < r - 1)
    (hlive1 :
      Not (e1 < q - 5 /\ gameF ((q - 5) - 1) e1 < q - 5))
    (hlive2 :
      Not (e2 < q - 5 /\ gameF ((q - 5) - 1) e2 < q - 5))
    (hclean1 : Not (ColTail gameF (q - 5) e1 (q + 3)))
    (hclean2 : Not (ColTail gameF (q - 5) e2 (q + 3))) :
    e1 = e2 := by
  have h1 := gameF_lag8_between_hosts_live_nonTail_is_currentFreeze
    hq hrv hstart howners hatomic hra hburn hdt hlower
      hde1 he1c hlive1 hclean1
  have h2 := gameF_lag8_between_hosts_live_nonTail_is_currentFreeze
    hq hrv hstart howners hatomic hra hburn hdt hlower
      hde2 he2c hlive2 hclean2
  exact gameRecurrenceModel.fixed_q_injective
    (by omega) (by omega) (h1.trans h2.symm)

/-- A column is free for the still-unpinned lag-eight target only if it is
not an old carry, has no old copy of the target in its fixed history, and is
not already committed to the current row's own freeze value.  This is a
broader notion than the empirical candidate filter, so excluding it is the
stronger statement. -/
def Lag8UnpinnedTargetCandidate (q e : Nat) : Prop :=
  Not (e < q - 5 /\ gameF ((q - 5) - 1) e < q - 5) /\
  Not (ColTail gameF (q - 5) e (q + 3)) /\
  Not (gameF (q - 5) e = q - 5)

/-- Exact all-index "next free seat" law.  Between the `q-2` lag-three
host and the `q+3` lag-eight host there is no unpinned target candidate at
all.  Intermediate live columns are either dirty with an old target relay
or are the single pinned freeze-now cell. -/
theorem gameF_lag8_no_unpinned_target_candidate_between_hosts
    {q r g d e : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hdt : d <= q - 5)
    (hlower : gameF (q - 5) d = q - 2)
    (hde : d < e) (hec : e < r - 1) :
    Not (Lag8UnpinnedTargetCandidate q e) := by
  rintro ⟨hlive, hclean, hnotPinned⟩
  exact hnotPinned
    (gameF_lag8_between_hosts_live_nonTail_is_currentFreeze
      hq hrv hstart howners hatomic hra hburn hdt hlower
        hde hec hlive hclean)

/-- Fully intrinsic W4 form.  The named lower freeze at `g` generates its
unique lag-three host `d` on row `q-5`, and the lag-eight target host at
`r-1` is the next unpinned target candidate after it. -/
theorem gameF_lag8_atomic_exact_next_unpinned_seat
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hsecond : gameF (q - 2) g = q - 2) :
    exists d,
      d < g /\ gameF (q - 5) d = q - 2 /\
      (forall d', d' <= q - 5 ->
        gameF (q - 5) d' = q - 2 -> d' = d) /\
      (forall e, d < e -> e < r - 1 ->
        Not (Lag8UnpinnedTargetCandidate q e)) := by
  have hgp : g < q - 2 := by omega
  have hgt : g < q - 5 := by omega
  rcases rowStartPropagation gameRecurrenceModel
      hsecond hgp hgt (by omega : q - 5 < q - 2) with
      ⟨d, hdg, hdhost⟩
  have hdrow : d <= q - 5 := by omega
  have hunique : forall d', d' <= q - 5 ->
      gameF (q - 5) d' = q - 2 -> d' = d := by
    intro d' hd'row hd'host
    exact gameRecurrenceModel.fixed_q_injective
      hd'row hdrow (hd'host.trans hdhost.symm)
  refine ⟨d, hdg, hdhost, hunique, ?_⟩
  intro e hde hec
  exact gameF_lag8_no_unpinned_target_candidate_between_hosts
    hq hrv hstart howners hatomic hra hburn hdrow hdhost hde hec

/-- The immediately preceding column `g=c-1` is not merely skipped: it is
a literal old relay column of the terminal target.  This needs no four-value
preload assumption.  A carry would freeze a smaller value in column `g`,
while a clean live seat would freeze the current row there; both contradict
the named `q-2` freeze in the same column. -/
theorem gameF_lag8_atomic_last_skip_is_target_colTail
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hsecond : gameF (q - 2) g = q - 2) :
    ColTail gameF (q - 5) g (q + 3) := by
  rcases gameF_lag8_atomic_exact_next_unpinned_seat
      hq hrv hstart howners hatomic hra hburn hsecond with
      ⟨d, hdg, hdhost, _hunique, _hnext⟩
  apply Classical.byContradiction
  intro hnoTail
  have hnotCarry :
      Not (g < q - 5 /\ gameF ((q - 5) - 1) g < q - 5) := by
    rintro ⟨hgrow, hlow⟩
    have hcol : g <= (q - 5) - 1 := by omega
    have hlowLe : gameF ((q - 5) - 1) g <= (q - 5) - 1 := by omega
    have hsmallFreeze := gameF_low_cell_has_rowstart hcol hlowLe
    exact gameF_freeze_column_unique
      hsmallFreeze.1 hsmallFreeze.2 (by omega) hsecond
  have hfreezeNow : gameF (q - 5) g = q - 5 :=
    gameF_lag8_between_hosts_live_nonTail_is_currentFreeze
      hq hrv hstart howners hatomic hra hburn (by omega) hdhost
        hdg (by omega) hnotCarry hnoTail
  exact gameF_freeze_column_unique
    (by omega : g < q - 5) hfreezeNow (by omega) hsecond

/-- Pairwise defect form: among any two distinct intermediate columns, at
least one is either an old carry or an old relay column of the target. -/
theorem gameF_lag8_between_hosts_pairwise_oldDefect
    {q r g d e1 e2 : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hdt : d <= q - 5)
    (hlower : gameF (q - 5) d = q - 2)
    (hde1 : d < e1) (he1c : e1 < r - 1)
    (hde2 : d < e2) (he2c : e2 < r - 1)
    (hne : Not (e1 = e2)) :
    ((e1 < q - 5 /\ gameF ((q - 5) - 1) e1 < q - 5) \/
      ColTail gameF (q - 5) e1 (q + 3)) \/
    ((e2 < q - 5 /\ gameF ((q - 5) - 1) e2 < q - 5) \/
      ColTail gameF (q - 5) e2 (q + 3)) := by
  apply Classical.byContradiction
  intro hnone
  have hlive1 :
      Not (e1 < q - 5 /\ gameF ((q - 5) - 1) e1 < q - 5) := by
    intro hcarry
    exact hnone (Or.inl (Or.inl hcarry))
  have hclean1 : Not (ColTail gameF (q - 5) e1 (q + 3)) := by
    intro htail
    exact hnone (Or.inl (Or.inr htail))
  have hlive2 :
      Not (e2 < q - 5 /\ gameF ((q - 5) - 1) e2 < q - 5) := by
    intro hcarry
    exact hnone (Or.inr (Or.inl hcarry))
  have hclean2 : Not (ColTail gameF (q - 5) e2 (q + 3)) := by
    intro htail
    exact hnone (Or.inr (Or.inr htail))
  have heq := gameF_lag8_between_hosts_atMostOne_live_nonTail
    hq hrv hstart howners hatomic hra hburn hdt hlower
      hde1 he1c hde2 he2c hlive1 hlive2 hclean1 hclean2
  exact hne heq

#print axioms gameF_lag8_lowerHost_column_gt_eleven
#print axioms gameF_lag8_between_hosts_live_nonTail_is_currentFreeze
#print axioms gameF_lag8_between_hosts_atMostOne_live_nonTail
#print axioms gameF_lag8_no_unpinned_target_candidate_between_hosts
#print axioms gameF_lag8_atomic_exact_next_unpinned_seat
#print axioms gameF_lag8_atomic_last_skip_is_target_colTail
#print axioms gameF_lag8_between_hosts_pairwise_oldDefect

end ChompLean
