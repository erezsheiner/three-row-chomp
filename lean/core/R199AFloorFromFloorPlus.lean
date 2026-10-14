import R198CausalMiddleCohortPullback

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# The actual AFloor is a counting consequence of Floor+

This file removes one of the two explicit numerical inputs of the causal
middle-cohort pullback.  The only remaining numerical hypothesis is the
actual diagonal `Floor+` inequality.  The proof counts nonblockers through
`n`: every such value has a unique diagonal owner, and `Floor+` puts every
owner at most `(2*n-5)/3` once `n >= 25`.  The first sixteen owners fit in
the same interval without a finite census.
-/

/-- Actual positive nonblockers through `n`. -/
noncomputable def gameFNonblockersThroughList (n : Nat) : List Nat := by
  classical
  exact (List.range' 1 n).filter (fun k => decide (Not (S gameF k)))

theorem gameF_mem_nonblockersThroughList {n k : Nat} :
    k ∈ gameFNonblockersThroughList n ↔
      0 < k ∧ k <= n ∧ Not (S gameF k) := by
  classical
  simp only [gameFNonblockersThroughList, List.mem_filter,
    decide_eq_true_eq, List.mem_range'_1]
  constructor
  . rintro ⟨⟨hk1, hkn⟩, hnot⟩
    exact ⟨by omega, by omega, hnot⟩
  . rintro ⟨hk, hkn, hnot⟩
    exact ⟨⟨by omega, by omega⟩, hnot⟩

/-- A canonical owner for a value which occurs on the diagonal.  Its value
away from the diagonal range is irrelevant. -/
noncomputable def gameFDiagonalOwner (k : Nat) : Nat := by
  classical
  exact if h : exists a, gameF a a = k then Classical.choose h else 0

theorem gameFDiagonalOwner_spec {k : Nat}
    (hkpos : 0 < k) (hnot : Not (S gameF k)) :
    gameF (gameFDiagonalOwner k) (gameFDiagonalOwner k) = k := by
  classical
  have hex : exists a, gameF a a = k := by
    by_cases h : exists a, gameF a a = k
    . exact h
    . exact False.elim
        (hnot ((gameF_blocker_iff_no_diagonal_owner hkpos).2 h))
  simp only [gameFDiagonalOwner, dif_pos hex]
  exact Classical.choose_spec hex

private theorem r199_nodup_map_of_injective_on
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

/-- `Floor+` alone implies the actual blocker-count floor used by R198.
No blocker-density theorem and no finite diagonal census is assumed. -/
theorem gameFBlockerCountThrough_AFloor_of_FloorPlus
    (hFloorPlus : forall {a k}, 16 <= a -> gameF a a = k ->
      3 * a + 5 <= 2 * k) :
    forall {v}, 26 <= v ->
      v <= 3 * gameFBlockerCountThrough (v - 1) + 2 := by
  classical
  intro v hv
  let n := v - 1
  let M := (2 * n - 5) / 3
  let xs := gameFNonblockersThroughList n
  let owners := xs.map gameFDiagonalOwner
  have hn : 25 <= n := by
    dsimp [n]
    omega
  have hM15 : 15 <= M := by
    dsimp [M]
    omega
  have hownerSpec : forall k, k ∈ xs ->
      gameF (gameFDiagonalOwner k) (gameFDiagonalOwner k) = k := by
    intro k hk
    have hkdata := gameF_mem_nonblockersThroughList.mp hk
    exact gameFDiagonalOwner_spec hkdata.1 hkdata.2.2
  have hownerLe : forall k, k ∈ xs -> gameFDiagonalOwner k <= M := by
    intro k hk
    have hkdata := gameF_mem_nonblockersThroughList.mp hk
    have hspec := hownerSpec k hk
    by_cases ha : 16 <= gameFDiagonalOwner k
    . have hfloor := hFloorPlus ha hspec
      dsimp [n, M] at *
      omega
    . dsimp [M]
      omega
  have hxsNodup : xs.Nodup := by
    dsimp [xs, gameFNonblockersThroughList]
    exact List.filter_sublist.nodup (List.nodup_range' 1)
  have hownersNodup : owners.Nodup := by
    dsimp [owners]
    apply r199_nodup_map_of_injective_on gameFDiagonalOwner xs hxsNodup
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

/-- The complete early-lag K=10 causal pullback with only `Floor+` left as
an explicit numerical input. -/
theorem actualBlockerMiddleCohortList_earlyLag_K10_causal_of_FloorPlus
    {u L : Nat}
    (hLu : L <= u)
    (hL : L = 13 ∨ L = 18 ∨ L = 20)
    (hRight : 25 <= u - L + 10)
    (hFloorPlus : forall {a k}, 16 <= a -> gameF a a = k ->
      3 * a + 5 <= 2 * k) :
    actualBlockerMiddleCohortList (u - L) 10 =
        causalBlockerMiddleCohortListFrom
          (u - L + 10) (u - L) 10 ∧
      u - L + 10 < u := by
  exact actualBlockerMiddleCohortList_earlyLag_K10_causal_of_floorPlus_AFloor
    hLu hL hRight
    (gameFBlockerCountThrough_AFloor_of_FloorPlus hFloorPlus)
    hFloorPlus

end ChompLean

#print axioms ChompLean.gameFBlockerCountThrough_AFloor_of_FloorPlus
#print axioms ChompLean.actualBlockerMiddleCohortList_earlyLag_K10_causal_of_FloorPlus
