import R130AssignmentNoGapReduction

set_option autoImplicit false

namespace ChompLean

/-!
Owner-coverage reduction for an induction on the blocker freeze upper rail.

The theorem is deliberately arithmetic/interface-level: `Av` is the target
prefix blocker count, `gv` its midpoint, while `Ak,gk` are the corresponding
coordinates for an earlier blocker.  No freeze order or assignment law is
assumed.  Earlier freeze owners are bounded only by the inductive upper-rail
hypothesis `r <= gk+1` and the strict growth of the midpoint forced by the
blocker-count increment.
-/

/-- A lower diagonal owner lies before the target midpoint from the banked
diagonal floor and blocker-count floor alone. -/
theorem diagonal_owner_le_target_midpoint
    {a k v Av gv : Nat}
    (hdiagFloor : 3 * a + 5 <= 2 * k)
    (hkv : k < v)
    (hAFloor : v <= 3 * Av + 2)
    (hmidUpper : v + Av < 2 * gv + 2) :
    a <= gv := by
  omega

/-- Actual bank-domain wrapper.  `Floor+` is only needed for owners at least
16.  Once the target is at least 26, the target AFloor and midpoint equations
already put every owner below 16 to the left of `gv`. -/
theorem diagonal_owner_le_target_midpoint_of_tail_floor
    {a k v Av gv : Nat}
    (hvBase : 26 <= v)
    (hdiagFloor : 16 <= a -> 3 * a + 5 <= 2 * k)
    (hkv : k < v)
    (hAFloor : v <= 3 * Av + 2)
    (hmidUpper : v + Av < 2 * gv + 2) :
    a <= gv := by
  by_cases ha : 16 <= a
  · exact diagonal_owner_le_target_midpoint
      (hdiagFloor ha) hkv hAFloor hmidUpper
  · omega

/-- Midpoints grow strictly between blocker values.  Consequently the
inductive upper rail for an earlier blocker puts its freeze owner at or to
the left of the current midpoint. -/
theorem earlier_freeze_le_target_midpoint
    {k v Ak Av gk gv r : Nat}
    (hkv : k < v)
    (hcount : Ak + 1 <= Av)
    (hmidKLower : 2 * gk <= k + Ak)
    (hmidVUpper : v + Av < 2 * gv + 2)
    (hfreezeIH : r <= gk + 1) :
    r <= gv := by
  omega

/-- Exact bridge to `LowerOwnerCoveredBy v gv` for an upper-rail induction.

`hdiagFloor` is the diagonal `Floor+` input.  In the row-start branch,
`hfreezeInductionData` packages only prefix count growth, floor bookkeeping,
and the upper-rail induction hypothesis for the lower blocker.  In
particular it does not assume global freeze order or max-plus service.
-/
theorem lowerOwnerCoveredBy_target_midpoint_of_upperRail_induction
    {v Av gv : Nat}
    (hAFloor : v <= 3 * Av + 2)
    (hmidVUpper : v + Av < 2 * gv + 2)
    (hdiagFloor : forall {k a},
      0 < k -> k < v -> a < k -> gameF a a = k ->
      3 * a + 5 <= 2 * k)
    (hfreezeInductionData : forall {k r},
      0 < k -> k < v -> r < k -> gameF k r = k ->
      exists Ak gk,
        Ak + 1 <= Av /\
        2 * gk <= k + Ak /\
        r <= gk + 1) :
    LowerOwnerCoveredBy v gv := by
  apply lowerOwnerCoveredBy_of_owner_bounds
  · intro k a hkpos hkv hak howner
    exact diagonal_owner_le_target_midpoint
      (hdiagFloor hkpos hkv hak howner) hkv hAFloor hmidVUpper
  · intro k r hkpos hkv hrk hstart
    rcases hfreezeInductionData hkpos hkv hrk hstart with
      ⟨Ak, gk, hcount, hmidKLower, hfreezeIH⟩
    exact earlier_freeze_le_target_midpoint hkv hcount hmidKLower
      hmidVUpper hfreezeIH

/-- Bank-domain version of the preceding bridge: Floor+ is requested only
on its proved tail `a>=16`, and `v>=26` is exactly the tail on which AFloor at
`v-1` is available without a finite check. -/
theorem lowerOwnerCoveredBy_target_midpoint_of_upperRail_induction_tail
    {v Av gv : Nat}
    (hvBase : 26 <= v)
    (hAFloor : v <= 3 * Av + 2)
    (hmidVUpper : v + Av < 2 * gv + 2)
    (hdiagFloor : forall {k a},
      0 < k -> k < v -> a < k -> gameF a a = k -> 16 <= a ->
      3 * a + 5 <= 2 * k)
    (hfreezeInductionData : forall {k r},
      0 < k -> k < v -> r < k -> gameF k r = k ->
      exists Ak gk,
        Ak + 1 <= Av /\
        2 * gk <= k + Ak /\
        r <= gk + 1) :
    LowerOwnerCoveredBy v gv := by
  apply lowerOwnerCoveredBy_of_owner_bounds
  · intro k a hkpos hkv hak howner
    exact diagonal_owner_le_target_midpoint_of_tail_floor hvBase
      (fun ha => hdiagFloor hkpos hkv hak howner ha)
      hkv hAFloor hmidVUpper
  · intro k r hkpos hkv hrk hstart
    rcases hfreezeInductionData hkpos hkv hrk hstart with
      ⟨Ak, gk, hcount, hmidKLower, hfreezeIH⟩
    exact earlier_freeze_le_target_midpoint hkv hcount hmidKLower
      hmidVUpper hfreezeIH

/-- Owner coverage and cleanliness at `gv+1` imply the desired one-sided
freeze rail.  This is the contradiction form of R130's exact-frontier
theorem and makes no max-plus assumption. -/
theorem gameF_freeze_le_midpoint_succ_of_owner_coverage
    {v r gv : Nat}
    (hvpos : 0 < v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v gv)
    (hclean : Not (ColHistPred gameF v (gv + 1) v)) :
    r <= gv + 1 := by
  apply Nat.le_of_not_gt
  intro hnot
  have hsr : gv < r := by omega
  have heq := gameF_freeze_eq_frontier_succ
    hvpos hrv hstart hsr howners hclean
  omega

/-- A lag-three host deletes only the newest-row arm of candidate history.
With the explicit host upper bound `previewHost <= gv`, the upper rail is
therefore reduced to old history before row `q`; the old-history premise is
not inferred from preview existence. -/
theorem gameF_freeze_le_midpoint_succ_of_lag3_and_old_history
    {q r gv previewHost : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (hpreviewLe : previewHost <= q)
    (hhostUpper : previewHost <= gv)
    (hcandidateInterior : 2 < gv + 1)
    (hhost : gameF q previewHost = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) gv)
    (hold : Not (ColHistPred gameF q (gv + 1) (q + 3))) :
    r <= gv + 1 := by
  have hne : gv + 1 ≠ previewHost := by omega
  have hclean := gameF_candidate_clean_of_old_history_and_distinct_preview
    hq hpreviewLe hcandidateInterior hhost hne hold
  exact gameF_freeze_le_midpoint_succ_of_owner_coverage
    (by omega) hrv hstart howners hclean

#print axioms diagonal_owner_le_target_midpoint
#print axioms diagonal_owner_le_target_midpoint_of_tail_floor
#print axioms earlier_freeze_le_target_midpoint
#print axioms lowerOwnerCoveredBy_target_midpoint_of_upperRail_induction
#print axioms lowerOwnerCoveredBy_target_midpoint_of_upperRail_induction_tail
#print axioms gameF_freeze_le_midpoint_succ_of_owner_coverage
#print axioms gameF_freeze_le_midpoint_succ_of_lag3_and_old_history

end ChompLean
