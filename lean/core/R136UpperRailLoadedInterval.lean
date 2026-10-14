import R134UpperRailCleanHistoryReduction
import R133TerminalTwoBlockerAmplifier
import TerminalBackfillSourceLoss

set_option autoImplicit false

namespace ChompLean

open ChompLean.R133TerminalTwoBlockerAmplifier

/-!
R136: the correct first-failure residue for the assignment upper rail.

At a first upper-rail failure, the inductive owner argument covers every
positive value below the target blocker by the midpoint `g`.  Therefore a
column `e` with `g < e < r`, where `r` is the target freeze, cannot be
clean.  If it were clean, R130's exact frontier theorem, applied at the
predecessor `e-1`, would force `r=e`.

Thus the whole open interval `(g,r)` is already loaded with the target in
old same-column history.  Before the actual freeze this is equivalently an
R15 `ParkedOnly` occurrence.  At the terminal column `r-1` it gives a
literal source loss on the edge `r-1 -> r`.
-/

/-- Lower-owner coverage is monotone in the certified column cutoff. -/
theorem lowerOwnerCoveredBy_mono
    {v s t : Nat} (hst : s <= t) (howners : LowerOwnerCoveredBy v s) :
    LowerOwnerCoveredBy v t := by
  intro k hkpos hkv
  rcases howners k hkpos hkv with
      ⟨a, has, hdiag⟩ | ⟨r, hrs, hrk, hstart⟩
  · exact Or.inl ⟨a, by omega, hdiag⟩
  · exact Or.inr ⟨r, by omega, hrk, hstart⟩

/-- A row-start output is on the MEX branch and hence is absent from its
own freeze source. -/
theorem gameF_rowstart_freeze_source_hole
    {v r : Nat} (hrv : r < v) (hstart : gameF v r = v) :
    Not (B gameF v r v) := by
  have hnotCarry : Not (r < v /\ gameF (v - 1) r < v) := by
    rintro ⟨hrv', hsmall⟩
    have hcarry := gameF_brouwerRecurrence.1 hrv' hsmall
    rw [hstart] at hcarry
    omega
  have hmex := gameF_brouwerRecurrence.2
    (q := v) (r := r) (Nat.le_of_lt hrv) hnotCarry
  simpa [hstart] using hmex.2.1

/-- Every column strictly after a complete lower-owner cutoff and strictly
before the target freeze is loaded by old target history.  Equivalently it
is `ParkedOnly`, and therefore belongs to the current source.

This is the local core of `FirstFailureLoadedInterval`; no midpoint formula
or first-failure bookkeeping is needed once owner coverage is available. -/
theorem gameF_ownerCovered_prefreeze_column_is_loaded
    {v r s e : Nat}
    (hvpos : 0 < v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v s)
    (hse : s < e)
    (her : e < r) :
    ColHistPred gameF v e v /\
      ParkedOnly gameF v e v /\
      B gameF v e v := by
  have hepos : 0 < e := by omega
  have hpredSucc : e - 1 + 1 = e := by omega
  have hsPred : s <= e - 1 := by omega
  have hownersPred : LowerOwnerCoveredBy v (e - 1) :=
    lowerOwnerCoveredBy_mono hsPred howners
  have hhist : ColHistPred gameF v e v := by
    by_cases hhist : ColHistPred gameF v e v
    · exact hhist
    · have heq := gameF_freeze_eq_frontier_succ
        hvpos hrv hstart (s := e - 1) (by omega) hownersPred
        (by simpa [hpredSucc] using hhist)
      rw [hpredSucc] at heq
      omega
  have hpark : ParkedOnly gameF v e v :=
    (gameF_parkedOnly_iff_colHistPred_before_freeze
      hrv hstart her).2 hhist
  exact ⟨hhist, hpark, parkedOnly_mem_current_source hpark⟩

/-- Interval form: a failed upper bound `s+1 < r` loads every column from
`s+1` through `r-1`. -/
theorem gameF_firstFailureLoadedInterval_of_ownerCoverage
    {v r s : Nat}
    (hvpos : 0 < v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v s)
    (hfailure : s + 1 < r) :
    (forall e, s + 1 <= e -> e < r ->
      ColHistPred gameF v e v /\
        ParkedOnly gameF v e v /\
        B gameF v e v) /\
    (B gameF v (r - 1) v /\
      Not (B gameF v r v) /\
      ParkedOnly gameF v (r - 1) v /\
      exists a, r <= a /\ a < v /\ gameF a (r - 1) = v) := by
  have hinterval : forall e, s + 1 <= e -> e < r ->
      ColHistPred gameF v e v /\
        ParkedOnly gameF v e v /\
        B gameF v e v := by
    intro e hleft hright
    exact gameF_ownerCovered_prefreeze_column_is_loaded
      hvpos hrv hstart howners (by omega) hright
  have hterminal := hinterval (r - 1) (by omega) (by omega)
  have hhole := gameF_rowstart_freeze_source_hole hrv hstart
  rcases hterminal.2.1.1 with ⟨a, hav, hra, hvalue⟩
  exact ⟨hinterval, hterminal.2.2, hhole, hterminal.2.1,
    ⟨a, by omega, hav, hvalue⟩⟩

/-- Full first-failure induction wrapper at the actual midpoint.  The
premises are exactly R133's owner-coverage induction data, except that the
clean-history premise has been replaced by the strict failure of the upper
rail.  Its conclusion is the loaded interval and terminal source-loss
packet, not a contradiction. -/
theorem gameF_firstFailureLoadedInterval
    (A : Nat -> Nat) {v r : Nat}
    (hvBase : 26 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hAFloor : v <= 3 * A (v - 1) + 2)
    (hdiagFloor : forall {k a},
      0 < k -> k < v -> a < k -> gameF a a = k -> 16 <= a ->
      3 * a + 5 <= 2 * k)
    (hfreezeInductionData : forall {k rk},
      0 < k -> k < v -> rk < k -> gameF k rk = k ->
      A (k - 1) + 1 <= A (v - 1) /\
        rk <= blockerMidpoint A k + 1)
    (hfailure : blockerMidpoint A v + 1 < r) :
    (forall e, blockerMidpoint A v + 1 <= e -> e < r ->
      ColHistPred gameF v e v /\
        ParkedOnly gameF v e v /\
        B gameF v e v) /\
    (B gameF v (r - 1) v /\
      Not (B gameF v r v) /\
      ParkedOnly gameF v (r - 1) v /\
      exists a, r <= a /\ a < v /\ gameF a (r - 1) = v) := by
  have hmidVUpper :
      v + A (v - 1) < 2 * blockerMidpoint A v + 2 := by
    unfold blockerMidpoint
    omega
  have howners : LowerOwnerCoveredBy v (blockerMidpoint A v) := by
    apply lowerOwnerCoveredBy_target_midpoint_of_upperRail_induction_tail
      hvBase hAFloor hmidVUpper hdiagFloor
    intro k rk hkpos hkv hrk hstartk
    rcases hfreezeInductionData hkpos hkv hrk hstartk with
      ⟨hcount, hrail⟩
    refine ⟨A (k - 1), blockerMidpoint A k, hcount, ?_, hrail⟩
    unfold blockerMidpoint
    omega
  exact gameF_firstFailureLoadedInterval_of_ownerCoverage
    (by omega) hrv hstart howners hfailure

/-! ## Preview-row consequence of a loaded first-failure interval -/

/-- Owner coverage through `s`, viewed on an earlier row `q`, saturates all
positive values at most `q` in every source column strictly after `s`.
Diagonal owners enter `R`; row-start owners have already reached their
constant branch and enter the current-row prefix. -/
theorem lowerOwnerCoveredBy_source_saturation_on_earlier_row
    {v s q e : Nat}
    (hqv : q < v)
    (hse : s < e)
    (heq : e <= q)
    (howners : LowerOwnerCoveredBy v s) :
    forall k, 0 < k -> k <= q -> B gameF q e k := by
  intro k hkpos hkq
  have hkv : k < v := by omega
  rcases howners k hkpos hkv with
      ⟨a, has, hdiag⟩ | ⟨r, hrs, hrk, hstart⟩
  · have hak : a < k := by
      have hgt := gameRecurrenceModel.diagonal_gt a
      change a < gameF a a at hgt
      rw [hdiag] at hgt
      exact hgt
    left
    refine ⟨a, by omega, ?_⟩
    have hmin : min a e = a := Nat.min_eq_left (by omega)
    simpa [hmin] using hdiag
  · right
    refine ⟨r, by omega, ?_⟩
    have hsmall : gameRecurrenceModel.f k r < k + 1 := by
      change gameF k r < k + 1
      rw [hstart]
      omega
    have hpersist := constant_from gameRecurrenceModel hrk
      hsmall (q - k)
    have hsum : k + (q - k) = q := by omega
    change gameF (k + (q - k)) r = gameF k r at hpersist
    rw [hsum, hstart] at hpersist
    exact hpersist

/-- A column beyond every lower owner cannot be on the low carry branch of
an earlier row.  A carried low predecessor would itself expose a row-start
owner at that column, contradicting the owner cutoff (or diagonal/row-start
disjointness). -/
theorem gameF_noCarry_after_lowerOwnerCutoff
    {v s q e : Nat}
    (hqv : q < v)
    (hse : s < e)
    (howners : LowerOwnerCoveredBy v s) :
    Not (e < q /\ gameF (q - 1) e < q) := by
  rintro ⟨heqStrict, hprevLow⟩
  have hePrev : e <= q - 1 := by omega
  have hrow := gameF_low_cell_has_rowstart hePrev (by omega)
  let k := gameF (q - 1) e
  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hkv : k < v := by
    dsimp [k]
    omega
  rcases howners k hkpos hkv with
      ⟨a, _has, hdiag⟩ | ⟨r, hrs, hrk, hstart⟩
  · exact disjoint_D_S gameRecurrenceModel
      ⟨a, hdiag⟩ ⟨e, hrow.1, hrow.2⟩
  · have her : e = r :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hrow.1) (Nat.le_of_lt hrk)
        (hrow.2.trans hstart.symm)
    omega

/-- If the lag-three preview host is strictly left of a loaded column, the
column's full target history cannot come from the preview row itself.
Causal depth three therefore pushes it strictly below the preview row. -/
theorem gameF_loaded_column_is_old_before_lagThree_preview
    {q H e : Nat}
    (hq : 1 <= q)
    (he : 2 < e)
    (hHq : H <= q)
    (hHe : H < e)
    (hhost : gameF q H = q + 3)
    (hfull : ColHistPred gameF (q + 3) e (q + 3)) :
    ColHistPred gameF q e (q + 3) := by
  rcases (gameF_colHist_causal_depth_three hq he).mp hfull with
      hold | hnew
  · exact hold
  · have heq : e = H :=
      gameRecurrenceModel.fixed_q_injective hnew.1 hHq
        (hnew.2.trans hhost.symm)
    omega

/-- A first upper-rail failure plus a preview host on the left creates a
whole run of strict high MEX outputs on the preview row.

For each `e in [s+1,r)`, the loaded interval first pushes the target history
below the preview row.  This proves `e<q`.  Lower-owner coverage supplies
`1..q`, the fixed column-0/column-2 rails supply `q+1,q+2`, and the preview
host supplies `q+3`.  The carry branch is excluded by the same owner cutoff,
so the cell's positive MEX is strictly larger than the target `q+3`. -/
theorem gameF_firstFailureLoadedInterval_preview_high_run
    {q r s H : Nat}
    (hq : 2 <= q)
    (hs : 2 <= s)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) s)
    (hfailure : s + 1 < r)
    (hHs : H <= s)
    (hHq : H <= q)
    (hhost : gameF q H = q + 3) :
    forall e, s + 1 <= e -> e < r ->
      ColHistPred gameF q e (q + 3) /\
        q + 3 < gameF q e := by
  have hloaded := gameF_firstFailureLoadedInterval_of_ownerCoverage
    (v := q + 3) (r := r) (s := s)
    (by omega) hrv hstart howners hfailure
  intro e hleft hright
  have hfull := (hloaded.1 e hleft hright).1
  have heThree : 2 < e := by omega
  have hHe : H < e := by omega
  have hold : ColHistPred gameF q e (q + 3) :=
    gameF_loaded_column_is_old_before_lagThree_preview
      (by omega) heThree hHq hHe hhost hfull
  have heq : e <= q := by
    rcases hold with ⟨a, hea, haq, _hvalue⟩
    omega
  have hlower : forall k, 0 < k -> k <= q -> B gameF q e k :=
    lowerOwnerCoveredBy_source_saturation_on_earlier_row
      (by omega) (by omega) heq howners
  have hsat : forall k, 0 < k -> k <= q + 3 -> B gameF q e k := by
    intro k hkpos hkupper
    by_cases hkq : k <= q
    · exact hlower k hkpos hkq
    · have hcases : k = q + 1 \/ k = q + 2 \/ k = q + 3 := by
        omega
      rcases hcases with rfl | rfl | rfl
      · right
        exact ⟨0, by omega, gameF_col0 q⟩
      · right
        exact ⟨2, by omega, gameF_col2_rail hq⟩
      · right
        exact ⟨H, hHe, hhost⟩
  have hnotCarry : Not (e < q /\ gameF (q - 1) e < q) :=
    gameF_noCarry_after_lowerOwnerCutoff
      (by omega) (by omega) howners
  have hmex := gameF_brouwerRecurrence.2 heq hnotCarry
  have houtPos : 0 < gameF q e := by
    have hgt := encoded_gt game_encodes heq
    omega
  have hhigh : q + 3 < gameF q e := by
    by_cases hhigh : q + 3 < gameF q e
    · exact hhigh
    · have houtLe : gameF q e <= q + 3 := by omega
      exact False.elim (hmex.2.1 (hsat (gameF q e) houtPos houtLe))
  exact ⟨hold, hhigh⟩

private theorem r136_nodup_map_of_injective_on
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

/-- Sharp counting consequence of the preview high run.

The interval has `ell = r-(s+1)` columns.  Fixed-row injectivity makes their
outputs distinct; strict row maximality places every output in the open
value interval `(q+3,d(q))`.  Hence

`ell <= d(q)-(q+4)`.

The old-history half of the high-run theorem also puts every interval column
strictly before `q`, so the terminal column gives the independent geometric
bound `r<=q`. -/
theorem gameF_firstFailure_preview_high_run_count
    {q r s H : Nat}
    (hq : 2 <= q)
    (hs : 2 <= s)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) s)
    (hfailure : s + 1 < r)
    (hHs : H <= s)
    (hHq : H <= q)
    (hhost : gameF q H = q + 3) :
    r <= q /\
      r - (s + 1) <= gameF q q - (q + 4) := by
  let ell := r - (s + 1)
  let cols := List.range' (s + 1) ell
  let outs := cols.map (fun e => gameF q e)
  have hrun := gameF_firstFailureLoadedInterval_preview_high_run
    hq hs hrv hstart howners hfailure hHs hHq hhost
  have hcolData : forall e, e ∈ cols ->
      ColHistPred gameF q e (q + 3) /\ q + 3 < gameF q e := by
    intro e he
    have herange := List.mem_range'_1.mp he
    have hleft : s + 1 <= e := herange.1
    have hright : e < r := by
      dsimp [ell] at herange
      omega
    exact hrun e hleft hright
  have hcolsNodup : cols.Nodup := by
    dsimp [cols]
    exact List.nodup_range' 1
  have houtNodup : outs.Nodup := by
    dsimp [outs]
    apply r136_nodup_map_of_injective_on
      (fun e => gameF q e) cols hcolsNodup
    intro x hx y hy hxy
    have hxHist := (hcolData x hx).1
    have hyHist := (hcolData y hy).1
    have hxq : x <= q := by
      rcases hxHist with ⟨a, hxa, haq, _⟩
      omega
    have hyq : y <= q := by
      rcases hyHist with ⟨a, hya, haq, _⟩
      omega
    exact gameRecurrenceModel.fixed_q_injective hxq hyq hxy
  have hsubset : outs ⊆
      List.range' (q + 4) (gameF q q - (q + 4)) := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨e, he, rfl⟩
    have hdata := hcolData e he
    have heqStrict : e < q := by
      rcases hdata.1 with ⟨a, hea, haq, _⟩
      omega
    have hrowMax := recurrence_strict_row_diagonal_maximal
      gameRecurrenceModel heqStrict
    change gameF q e < gameF q q at hrowMax
    have hbase : q + 4 <= gameF q q := by omega
    have hsum : q + 4 + (gameF q q - (q + 4)) = gameF q q :=
      Nat.add_sub_of_le hbase
    apply List.mem_range'_1.mpr
    constructor
    · omega
    · rw [hsum]
      exact hrowMax
  have hbound := nodup_subset_length_le houtNodup hsubset
  have hcount :
      r - (s + 1) <= gameF q q - (q + 4) := by
    simpa [outs, cols, ell] using hbound
  have hterminal := hrun (r - 1) (by omega) (by omega)
  have hrq : r <= q := by
    rcases hterminal.1 with ⟨a, hra, haq, _⟩
    omega
  exact ⟨hrq, hcount⟩

/-- E9/J9 specialization of the high-run count.  The subtraction-free
diagonal ceiling `d(q)+9<=2q` gives only

`ell+13<=q`.

This is recorded because it is the strongest consequence of E9 and row
injectivity alone; in the midpoint regime the separate `r<=q` bound is
usually much stronger. -/
theorem gameF_firstFailure_preview_high_run_count_of_E9
    {q r s H : Nat}
    (hq : 2 <= q)
    (hs : 2 <= s)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) s)
    (hfailure : s + 1 < r)
    (hHs : H <= s)
    (hHq : H <= q)
    (hhost : gameF q H = q + 3)
    (hE9 : gameF q q + 9 <= 2 * q) :
    r - (s + 1) + 13 <= q := by
  have hcount := (gameF_firstFailure_preview_high_run_count
    hq hs hrv hstart howners hfailure hHs hHq hhost).2
  have hterminal := gameF_firstFailureLoadedInterval_preview_high_run
    hq hs hrv hstart howners hfailure hHs hHq hhost
      (r - 1) (by omega) (by omega)
  have hrowMax : gameF q (r - 1) < gameF q q := by
    rcases hterminal.1 with ⟨a, hra, haq, _⟩
    exact recurrence_strict_row_diagonal_maximal
      gameRecurrenceModel (by omega)
  omega

#print axioms lowerOwnerCoveredBy_mono
#print axioms gameF_rowstart_freeze_source_hole
#print axioms gameF_ownerCovered_prefreeze_column_is_loaded
#print axioms gameF_firstFailureLoadedInterval_of_ownerCoverage
#print axioms gameF_firstFailureLoadedInterval
#print axioms lowerOwnerCoveredBy_source_saturation_on_earlier_row
#print axioms gameF_noCarry_after_lowerOwnerCutoff
#print axioms gameF_loaded_column_is_old_before_lagThree_preview
#print axioms gameF_firstFailureLoadedInterval_preview_high_run
#print axioms gameF_firstFailure_preview_high_run_count
#print axioms gameF_firstFailure_preview_high_run_count_of_E9

end ChompLean
