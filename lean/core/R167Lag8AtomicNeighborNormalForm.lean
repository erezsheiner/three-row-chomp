import R166Lag8NeighborRelaySeedNormalForm
import R165Lag8HorizontalSeededChronologyNormalForm

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight atomic branch: exact neighbour and owner-channel normal form

Write `v=q+3` and suppose the failed band is atomic, `r=g+2`.  Then the
first empirical neighbour column is exactly `g`, at row `t=q-3=v-6`.

Owner coverage saturates the source at `(t,g)` at every positive value
below `v`, with one possible exception: `t` itself may be a row-start whose
freeze column is exactly `g`.  The carry branch contributes the companion
escape, an already frozen sibling below `t`.  This gives the exact menu

```
an old/current sibling owns column g
or F(t,g)>v.
```

The six fixed target rails force `11<=g`; since the row-`t` target host is
the fixed column-nine rail, the equality branch is impossible.  If the
second empirical neighbour cell freezes `t+1=q-2` at `g`, the sibling/carry
branch disappears as well, leaving only the strict-high branch.

The second half separates the two left-owner arms.  A row-start owner of
`q` forces a unique row-`t` prehost `b` with `10<=b<owner<=g`.  A diagonal
owner either has no row-prefix echo on row `t`, or every such echo has the
same sandwich `10<=b<owner<=g`.  Thus the still-missing chronology is the
rightmost endpoint `b=g`, which neither left-owner arm can realize.
-/

/-- Source saturation at the atomic neighbour cell, except for the current
row value itself. -/
theorem gameF_lag8_atomic_neighbor_saturated_except_current
    {q g k : Nat}
    (hq : 26 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hgq : g + 2 <= q - 5)
    (hkpos : 0 < k)
    (hkv : k < q + 3)
    (hne : k ≠ q - 3) :
    B gameF (q - 3) g k := by
  rcases howners k hkpos hkv with
      ⟨a, hag, hdiag⟩ | ⟨s, hsg, hs, hrow⟩
  · left
    refine ⟨a, by omega, ?_⟩
    have hmin : min a g = a := Nat.min_eq_left hag
    simpa [hmin] using hdiag
  · by_cases hsgStrict : s < g
    · exact rowstart_freeze_lt_source_is_covered
        gameRecurrenceModel (by omega) hs hrow hsgStrict
    · have hsgEq : s = g := by omega
      subst s
      by_cases hkt : k < q - 3
      · left
        refine ⟨k, hkt, ?_⟩
        have hmin : min k g = g := Nat.min_eq_right (by omega)
        simpa [hmin] using hrow
      · have htk : q - 3 < k := by omega
        right
        rcases rowStartPropagation gameRecurrenceModel (q := q - 3)
            hrow hs (by omega) htk with ⟨b, hbg, hvalue⟩
        change gameF (q - 3) b = k at hvalue
        exact ⟨b, hbg, hvalue⟩

/-- Recurrence-only atomic menu before the fixed target rail is used.  The
first branch names the blocker whose constant column is being carried; it
also includes the current-row freeze `k=q-3`. -/
theorem gameF_lag8_atomic_neighbor_recurrence_menu
    {q g : Nat}
    (hq : 26 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hgq : g + 2 <= q - 5) :
    (exists k,
      g < k /\ k <= q - 3 /\ gameF k g = k /\
        gameF (q - 3) g = k) \/
      q + 3 <= gameF (q - 3) g := by
  by_cases hcarry :
      g < q - 3 /\ gameF ((q - 3) - 1) g < q - 3
  · have hout := gameF_brouwerRecurrence.1 hcarry.1 hcarry.2
    let k := gameF ((q - 3) - 1) g
    have hrow := gameF_low_cell_has_rowstart
      (q := (q - 3) - 1) (c := g) (by omega) (by omega)
    refine Or.inl ⟨k, ?_, ?_, ?_, ?_⟩
    · dsimp [k]
      exact hrow.1
    · dsimp [k]
      omega
    · dsimp [k]
      exact hrow.2
    · dsimp [k]
      exact hout
  · have hmex := gameF_brouwerRecurrence.2
      (q := q - 3) (r := g) (by omega) hcarry
    by_cases heq : gameF (q - 3) g = q - 3
    · left
      exact ⟨q - 3, by omega, by omega, heq, heq⟩
    · right
      apply Nat.le_of_not_gt
      intro hlt
      exact hmex.2.1
        (gameF_lag8_atomic_neighbor_saturated_except_current
          hq howners hgq hmex.1 hlt heq)

/-- No occurrence of `q` is possible in columns `0,...,9` of row `q-3`.
The statement is independent of the lag-eight frame and uses only the
proved early rails. -/
theorem gameF_qminus3_qHost_column_ge10
    {q b : Nat}
    (hq : 26 <= q)
    (hbq : b <= q - 3)
    (hhost : gameF (q - 3) b = q) :
    10 <= b := by
  apply Nat.le_of_not_gt
  intro hb10
  have hcases :
      b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
      b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · rw [gameF_col0] at hhost
    omega
  · rw [gameF_col1_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col2_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col3_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col4_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col5_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col6_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col7_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col8_rail (q := q - 3) (by omega)] at hhost
    omega
  · rw [gameF_col9_rail (q := q - 3) (by omega)] at hhost
    omega

/-- Full atomic normal form after inserting the six target rails.  The
failed-band cutoff is already at least eleven, so the fixed target at column
nine cannot be the current value. -/
theorem gameF_lag8_atomic_neighbor_exact_normalForm
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hatomic : r = g + 2) :
    11 <= g /\
      ((exists k,
          g < k /\ k <= q - 3 /\ gameF k g = k /\
            gameF (q - 3) g = k) \/
        q + 3 < gameF (q - 3) g) := by
  have hg11 := gameF_lag8_failed_band_cutoff_atLeast_eleven
    hq hrv hstart howners hfailure hra hburn
  have h9raw := gameF_col9_rail (q := q - 3) (by omega)
  have h9 : gameF (q - 3) 9 = q + 3 := by
    calc
      gameF (q - 3) 9 = (q - 3) + 6 := h9raw
      _ = q + 3 := by omega
  refine ⟨hg11, ?_⟩
  rcases gameF_lag8_atomic_neighbor_recurrence_menu
      hq howners (by omega) with hsibling | hhigh
  · exact Or.inl hsibling
  · right
    have hne : gameF (q - 3) g ≠ q + 3 := by
      intro hEq
      have hcols : g = 9 :=
        gameRecurrenceModel.fixed_q_injective
          (by omega) (by omega) (hEq.trans h9.symm)
      omega
    omega

/-- The second empirical neighbour freeze kills the sibling/carry branch.
The first atomic neighbour is therefore strictly above the target. -/
theorem gameF_lag8_atomic_secondNeighbor_forces_strictHigh
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hatomic : r = g + 2)
    (hsecond : gameF (q - 2) g = q - 2) :
    11 <= g /\ q + 3 < gameF (q - 3) g := by
  rcases gameF_lag8_atomic_neighbor_exact_normalForm
      hq hrv hstart howners hfailure hra hburn hatomic with
      ⟨hg11, hsibling | hhigh⟩
  · rcases hsibling with ⟨k, hgk, hkt, hkfreeze, htvalue⟩
    have hrow : (q - 2) - 1 = q - 3 := by omega
    have hprev : gameF ((q - 2) - 1) g < q - 2 := by
      rw [hrow, htvalue]
      omega
    have hcopy := gameF_brouwerRecurrence.1
      (q := q - 2) (r := g) (by omega) hprev
    rw [hrow, htvalue, hsecond] at hcopy
    omega
  · exact ⟨hg11, hhigh⟩

/-- Atomic separation of the two left-owner arms at the first neighbour
source.  The diagonal arm is pure diagonal-prefix unless it has a late
row-`q-3` echo; the row-start arm necessarily has such an echo. -/
theorem gameF_lag8_atomic_ownerArms_prefix_normalForm
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hatomic : r = g + 2) :
    (exists d,
      7 < d /\ d <= g /\ gameF d d = q /\
      DiagPrefix gameF (q - 3) g q /\
      Not (ColTail gameF (q - 3) g q) /\
      (Not (C gameF (q - 3) g q) \/
        exists b, 10 <= b /\ b < d /\ gameF (q - 3) b = q)) \/
    (exists s b,
      10 <= b /\ b < s /\ s <= g /\ s < q /\
      gameF q s = q /\ gameF (q - 3) b = q /\
      C gameF (q - 3) g q /\
      Not (DiagPrefix gameF (q - 3) g q) /\
      Not (ColTail gameF (q - 3) g q)) := by
  have htwo := gameF_lag8_preview_leftOwner_exact_twoArm_normalForm
    hq hrv hstart howners hfailure hra hburn
  have hnoColRaw :=
    (gameF_lag8_failed_band_neighbor_q_exact_owner_channel
      (v := q + 3) (r := r) (g := g)
      (by omega) howners hfailure (by omega)).2
  have hnoCol : Not (ColTail gameF (q - 3) g q) := by
    simpa [hatomic] using hnoColRaw
  rcases htwo.2.2 with ⟨d, harm⟩ | ⟨s, harm⟩
  · left
    have henv := harm.1
    have hdiag := harm.2.1
    have hdq5 : d < q - 5 := henv.2.2.1.2
    have hdq3 : d < q - 3 := by omega
    have hD : DiagPrefix gameF (q - 3) g q :=
      ⟨d, hdq3, henv.1, hdiag⟩
    refine ⟨d, henv.2.2.1.1, henv.1, hdiag, hD, hnoCol, ?_⟩
    by_cases hC : C gameF (q - 3) g q
    · right
      rcases hC with ⟨b, hbg, hbval⟩
      have hbq : b <= q - 3 := by omega
      have h10 := gameF_qminus3_qHost_column_ge10 hq hbq hbval
      have hbd :=
        (gameF_dynamic_qHost_leftDiagonal_sandwich harm hbq hbval).1
      exact ⟨b, h10, hbd, hbval⟩
    · exact Or.inl hC
  · right
    have henv := harm.1
    have hsq := harm.2.1
    have hrow := harm.2.2.1
    have hs5 : s < q - 5 := henv.2.2.1.2
    have hs3 : s < q - 3 := by omega
    have hsg : s <= g := henv.1
    rcases rowStartPropagation gameRecurrenceModel (q := q - 3)
        hrow hsq hs3 (by omega) with ⟨b, hbs, hbval⟩
    change gameF (q - 3) b = q at hbval
    have hbq : b <= q - 3 := by omega
    have h10 := gameF_qminus3_qHost_column_ge10 hq hbq hbval
    have hC : C gameF (q - 3) g q := ⟨b, by omega, hbval⟩
    have hnoDiag : Not (DiagPrefix gameF (q - 3) g q) := by
      rintro ⟨a, _hat, _hag, hdiag⟩
      exact disjoint_D_S gameRecurrenceModel
        ⟨a, hdiag⟩ ⟨s, hsq, hrow⟩
    exact ⟨s, b, h10, hbs, hsg, hsq, hrow, hbval,
      hC, hnoDiag, hnoCol⟩

#print axioms gameF_lag8_atomic_neighbor_saturated_except_current
#print axioms gameF_lag8_atomic_neighbor_recurrence_menu
#print axioms gameF_qminus3_qHost_column_ge10
#print axioms gameF_lag8_atomic_neighbor_exact_normalForm
#print axioms gameF_lag8_atomic_secondNeighbor_forces_strictHigh
#print axioms gameF_lag8_atomic_ownerArms_prefix_normalForm

end ChompLean
