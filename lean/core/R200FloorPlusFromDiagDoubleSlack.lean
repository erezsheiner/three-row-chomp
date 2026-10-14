import R199AFloorFromFloorPlus
import EarlyEvenConstantRails

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# Actual Floor+ from the sharp diagonal ceiling

The prose bank derives Floor+ by combining the exact-slot lower identity
with the sharp blocker-count ceiling.  This file ports that composition to
the actual `gameF` definitions.

The exact-slot half is unconditional from the already proved overlap
ledger.  The blocker-count ceiling is proved from a single explicit input:
the all-index `ActualDiagDoubleSlack` input. This file proves the conditional composition; `R201DiagDoubleSlackCeilingChain` supplies that input in the present package.
-/

/-- Subtraction-free form of `d(a) <= 2*a-2` on its sharp tail. -/
def ActualDiagDoubleSlack : Prop :=
  forall a, 9 <= a -> gameF a a + 2 <= 2 * a

private theorem r200_nodup_map_of_injective_on
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

private theorem r200_actual_blocker_nonblocker_partition (n : Nat) :
    n = gameFBlockerCountThrough n +
      (gameFNonblockersThroughList n).length := by
  classical
  have hpartition := List.length_eq_countP_add_countP
    (fun k : Nat => decide (S gameF k)) (l := List.range' 1 n)
  simp only [List.countP_eq_length_filter] at hpartition
  simpa [gameFBlockerCountThrough, gameFBlockersThroughList,
    gameFNonblockersThroughList] using hpartition

/-- Actual ExactSlot / uniform-reemission lower bound, in a
subtraction-free form:

`d(a) >= 2*a+1-A(a)` is written as `2*a+1 <= d(a)+A(a)`.

This is unconditional: every nonblocker through `a` has a distinct
diagonal owner counted by the overlap ledger's `L(a)` packet. -/
theorem gameF_exactSlot_lower (a : Nat) :
    2 * a + 1 <= gameF a a + gameFBlockerCountThrough a := by
  classical
  let xs := gameFNonblockersThroughList a
  let owners := xs.map gameFDiagonalOwner
  have hownerSpec : forall k, k ∈ xs ->
      gameF (gameFDiagonalOwner k) (gameFDiagonalOwner k) = k := by
    intro k hk
    have hkdata := gameF_mem_nonblockersThroughList.mp hk
    exact gameFDiagonalOwner_spec hkdata.1 hkdata.2.2
  have hxsNodup : xs.Nodup := by
    dsimp [xs, gameFNonblockersThroughList]
    exact List.filter_sublist.nodup (List.nodup_range' 1)
  have hownersNodup : owners.Nodup := by
    dsimp [owners]
    apply r200_nodup_map_of_injective_on gameFDiagonalOwner xs hxsNodup
    intro x hx y hy hxy
    have hxspec := hownerSpec x hx
    have hyspec := hownerSpec y hy
    rw [hxy] at hxspec
    exact hxspec.symm.trans hyspec
  have hownersSub : owners ⊆ PastAtMostRowDiagonalIndices a := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨k, hk, rfl⟩
    have hkdata := gameF_mem_nonblockersThroughList.mp hk
    have hspec := hownerSpec k hk
    have hgt := gameRecurrenceModel.diagonal_gt (gameFDiagonalOwner k)
    change gameFDiagonalOwner k <
      gameF (gameFDiagonalOwner k) (gameFDiagonalOwner k) at hgt
    apply mem_pastAtMostRowDiagonalIndices_iff.mpr
    constructor
    . omega
    . omega
  have hcap0 := nodup_subset_length_le hownersNodup hownersSub
  have hcap : xs.length <= PastAtMostRowDiagonalCount a := by
    simpa [owners, PastAtMostRowDiagonalCount] using hcap0
  have hpartition := r200_actual_blocker_nonblocker_partition a
  have henv := gameF_ledger_lower_envelope_with_L a
  dsimp [xs] at hcap
  omega

/-- The sharp blocker-prefix ceiling follows from DiagDoubleSlack.  It is
written in the uniform parity-free form equivalent to
`A(a) <= ceil(a/2)-2`:

`2*A(a)+4 <= a+1` for `a>=16`.

The proof inserts the diagonal values with indices
`0,...,floor(a/2)+1` into the nonblocker prefix.  The two edge indices are
exactly where `d(i)<=2*i-2` is needed. -/
theorem gameFBlockerCountThrough_ceiling_of_diagDoubleSlack
    (hDDS : ActualDiagDoubleSlack) :
    forall {a}, 16 <= a ->
      2 * gameFBlockerCountThrough a + 4 <= a + 1 := by
  classical
  intro a ha
  let idxs := List.range (a / 2 + 2)
  let vals := idxs.map (fun i => gameF i i)
  let xs := gameFNonblockersThroughList a
  have hidxsNodup : idxs.Nodup := by
    dsimp [idxs]
    exact List.nodup_range
  have hvalsNodup : vals.Nodup := by
    dsimp [vals]
    apply r200_nodup_map_of_injective_on
      (fun i => gameF i i) idxs hidxsNodup
    intro i _hi j _hj hij
    exact diagonal_injective gameRecurrenceModel hij
  have hvalsSub : vals ⊆ xs := by
    intro k hk
    rcases List.mem_map.mp hk with ⟨i, hi, rfl⟩
    have hiBound : i < a / 2 + 2 := by
      exact List.mem_range.mp hi
    have hpos0 := gameRecurrenceModel.diagonal_gt i
    have hpos : 0 < gameF i i := Nat.zero_lt_of_lt hpos0
    have hle : gameF i i <= a := by
      by_cases hi9 : 9 <= i
      . have hsharp := hDDS i hi9
        omega
      . by_cases hi8 : i = 8
        . subst i
          rw [gameF_diag_eight]
          omega
        . have hcap := recurrence_diagonal_source_capacity
            gameRecurrenceModel i
          change gameF i i <= i + i + 1 at hcap
          omega
    have hnot : Not (S gameF (gameF i i)) := by
      intro hS
      exact disjoint_D_S gameRecurrenceModel ⟨i, rfl⟩ hS
    apply gameF_mem_nonblockersThroughList.mpr
    exact ⟨hpos, hle, hnot⟩
  have hcap0 := nodup_subset_length_le hvalsNodup hvalsSub
  have hcap : a / 2 + 2 <= xs.length := by
    simpa [vals, idxs] using hcap0
  have hpartition := r200_actual_blocker_nonblocker_partition a
  dsimp [xs] at hcap
  omega

/-- The actual bank-domain Floor+ theorem, conditional only on the `ActualDiagDoubleSlack` supplier, proved later in `R201DiagDoubleSlackCeilingChain`. -/
theorem gameF_FloorPlus_of_diagDoubleSlack
    (hDDS : ActualDiagDoubleSlack) :
    forall {a k}, 16 <= a -> gameF a a = k ->
      3 * a + 5 <= 2 * k := by
  intro a k ha hak
  have hslot := gameF_exactSlot_lower a
  have hcount :=
    gameFBlockerCountThrough_ceiling_of_diagDoubleSlack hDDS ha
  rw [hak] at hslot
  omega

/-- R198's complete early-lag K=10 causal pullback, now conditional on the
single explicit DiagDoubleSlack supplier rather than Floor+ or AFloor. -/
theorem actualBlockerMiddleCohortList_earlyLag_K10_causal_of_diagDoubleSlack
    (hDDS : ActualDiagDoubleSlack)
    {u L : Nat}
    (hLu : L <= u)
    (hL : L = 13 ∨ L = 18 ∨ L = 20)
    (hRight : 25 <= u - L + 10) :
    actualBlockerMiddleCohortList (u - L) 10 =
        causalBlockerMiddleCohortListFrom
          (u - L + 10) (u - L) 10 ∧
      u - L + 10 < u := by
  exact actualBlockerMiddleCohortList_earlyLag_K10_causal_of_FloorPlus
    hLu hL hRight (gameF_FloorPlus_of_diagDoubleSlack hDDS)

end ChompLean

#print axioms ChompLean.gameF_exactSlot_lower
#print axioms ChompLean.gameFBlockerCountThrough_ceiling_of_diagDoubleSlack
#print axioms ChompLean.gameF_FloorPlus_of_diagDoubleSlack
#print axioms ChompLean.actualBlockerMiddleCohortList_earlyLag_K10_causal_of_diagDoubleSlack
