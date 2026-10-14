import R199AFloorFromFloorPlus

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R201: the weak overlap envelope already causalizes the middle cohort

The earlier R198--R200 route used the sharp diagonal `Floor+` and therefore
appeared to depend on `DiagDoubleSlack`.  That strength is unnecessary.
The unconditional R55 envelope

`a + 1 + floor((a+1)/2) <= d(a)`

already (1) bounds the number of diagonal values below a target strongly
enough to imply AFloor, and (2) puts every lower diagonal owner before the
target midpoint.  Hence the early-lag K=10 cohort is causal with no numerical
hypothesis at all.
-/

private theorem r201_nodup_map_of_injective_on
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
      . intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hay⟩
        have hay' : a = y :=
          hinj a (by simp) y (by simp [hy]) hay.symm
        subst y
        exact hxs.1 hy
      . apply ih hxs.2
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

/-- The actual AFloor count inequality follows from the unconditional R55
`3/2` overlap envelope; sharp Floor+ is not needed. -/
theorem gameFBlockerCountThrough_AFloor_of_overlapEnvelope :
    forall {v}, 26 <= v ->
      v <= 3 * gameFBlockerCountThrough (v - 1) + 2 := by
  classical
  intro v hv
  let n := v - 1
  let M := (2 * n - 2) / 3
  let xs := gameFNonblockersThroughList n
  let owners := xs.map gameFDiagonalOwner
  have hownerSpec : forall k, k ∈ xs ->
      gameF (gameFDiagonalOwner k) (gameFDiagonalOwner k) = k := by
    intro k hk
    have hkdata := gameF_mem_nonblockersThroughList.mp hk
    exact gameFDiagonalOwner_spec hkdata.1 hkdata.2.2
  have hownerLe : forall k, k ∈ xs -> gameFDiagonalOwner k <= M := by
    intro k hk
    have hkdata := gameF_mem_nonblockersThroughList.mp hk
    have hspec := hownerSpec k hk
    have henv := gameF_overlap_env_lower_bound (gameFDiagonalOwner k)
    rw [hspec] at henv
    dsimp [n, M] at *
    omega
  have hxsNodup : xs.Nodup := by
    dsimp [xs, gameFNonblockersThroughList]
    exact List.filter_sublist.nodup (List.nodup_range' 1)
  have hownersNodup : owners.Nodup := by
    dsimp [owners]
    apply r201_nodup_map_of_injective_on gameFDiagonalOwner xs hxsNodup
    intro x hx y hy hxy
    have hxspec := hownerSpec x hx
    have hyspec := hownerSpec y hy
    rw [hxy] at hxspec
    exact hxspec.symm.trans hyspec
  have hownersSub : owners ⊆ List.range (M + 1) := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨k, hk, rfl⟩
    exact List.mem_range.mpr (by have := hownerLe k hk; omega)
  have hcap0 := nodup_subset_length_le hownersNodup hownersSub
  have hcap : xs.length <= M + 1 := by
    simpa [owners] using hcap0
  have hpartition0 := List.length_eq_countP_add_countP
    (fun k : Nat => decide (S gameF k)) (l := List.range' 1 n)
  simp only [List.countP_eq_length_filter] at hpartition0
  have hpartition :
      n = gameFBlockerCountThrough n + xs.length := by
    simpa [gameFBlockerCountThrough, gameFBlockersThroughList,
      xs, gameFNonblockersThroughList] using hpartition0
  dsimp [n, M] at hcap hpartition
  omega

/-- A lower diagonal owner is before the target midpoint using only the R55
overlap envelope and AFloor. -/
theorem diagonal_owner_le_target_midpoint_of_overlapEnvelope
    {a k v Av gv : Nat}
    (hdiag : gameF a a = k)
    (hkv : k < v)
    (hAFloor : v <= 3 * Av + 2)
    (hmidUpper : v + Av < 2 * gv + 2) :
    a <= gv := by
  have henv := gameF_overlap_env_lower_bound a
  rw [hdiag] at henv
  omega

/-- The exact visibility supplier needed by R198 is unconditional on every
right edge at least 25. -/
theorem actualNonblockerSublevelVisible_of_overlapEnvelope
    {T : Nat}
    (hT : 25 <= T) :
    ActualNonblockerSublevelVisible T T := by
  intro v k hkpos hkv hupper hnot
  rcases gameRecurrenceModel.opening_cover hkpos with hD | hS
  . rcases hD with ⟨a, hak, ha⟩
    have haT : a <= T := by
      by_cases hv : 26 <= v
      . have hmidUpper :
            v + gameFBlockerCountThrough (v - 1) <
              2 * actualBlockerMidpoint v + 2 := by
          unfold actualBlockerMidpoint countMidpoint
          omega
        have hag := diagonal_owner_le_target_midpoint_of_overlapEnvelope
          (a := a) (k := k) (v := v)
          (Av := gameFBlockerCountThrough (v - 1))
          (gv := actualBlockerMidpoint v)
          ha hkv
          (gameFBlockerCountThrough_AFloor_of_overlapEnvelope hv)
          hmidUpper
        omega
      . omega
    exact ⟨⟨a, by omega⟩, ha⟩
  . exact False.elim (hnot hS)

/-- The complete actual K-cohort is determined by the diagonal prefix through
the right edge, with no Floor+, AFloor, or DiagDoubleSlack premise. -/
theorem actualBlockerMiddleCohortList_eq_causalFrom_rightEdge_unconditional
    {center K : Nat}
    (hRight : 25 <= center + K) :
    actualBlockerMiddleCohortList center K =
      causalBlockerMiddleCohortListFrom (center + K) center K := by
  apply actualBlockerMiddleCohortList_eq_causalFrom_of_visibility
  exact actualNonblockerSublevelVisible_of_overlapEnvelope hRight

/-- Direct unconditional W4 wrapper.  At lags 13, 18, and 20, the complete
K=10 middle cohort is computed from a strict induction prefix below `u`. -/
theorem actualBlockerMiddleCohortList_earlyLag_K10_causal_unconditional
    {u L : Nat}
    (hLu : L <= u)
    (hL : L = 13 ∨ L = 18 ∨ L = 20)
    (hRight : 25 <= u - L + 10) :
    actualBlockerMiddleCohortList (u - L) 10 =
        causalBlockerMiddleCohortListFrom
          (u - L + 10) (u - L) 10 ∧
      u - L + 10 < u := by
  constructor
  . exact
      actualBlockerMiddleCohortList_eq_causalFrom_rightEdge_unconditional
        hRight
  . exact lag13_18_20_K10_visible_horizon_before_target hLu hL

end ChompLean

#print axioms ChompLean.gameFBlockerCountThrough_AFloor_of_overlapEnvelope
#print axioms ChompLean.diagonal_owner_le_target_midpoint_of_overlapEnvelope
#print axioms ChompLean.actualNonblockerSublevelVisible_of_overlapEnvelope
#print axioms ChompLean.actualBlockerMiddleCohortList_eq_causalFrom_rightEdge_unconditional
#print axioms ChompLean.actualBlockerMiddleCohortList_earlyLag_K10_causal_unconditional
