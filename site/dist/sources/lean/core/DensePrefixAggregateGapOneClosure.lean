import AggregateFcrossHall
import DensePrefixPenultimateFreezeKill
import R132OldLossTerminalCellKill

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
Arithmetic closure of the dense `b_i = 2*i` prefix.

The first theorem isolates the exact cancellation used after FreezeOrder has
removed the inversion term from PiZero. Aggregate fixed-column capacity then
leaves no room for the newest load. The second theorem records what survives
without FreezeOrder: the newest load is paid only by earlier inversions, so the
zero-load conclusion is no longer available.

The final theorem is the shortest contradiction for the R141/A_k interface:
rank two is forced to freeze at column three, hence its blocker value four is a
forbidden gap-one freeze. `GapOneKill` remains an explicit hypothesis of this abstract interface.
The package separately provides the actual-game theorem
`gameF_gap_one_kill` in `PenultimateFreezeGlobalKill`.
-/

/-- Sum of `f 0,...,f (n-1)`, kept elementary so this closure kernel does
not need a separate big-operator import. -/
def densePrefixSum (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => densePrefixSum f n + f n

theorem densePrefixSum_congr
    {f g : Nat -> Nat} {n : Nat}
    (h : forall i, i < n -> f i = g i) :
    densePrefixSum f n = densePrefixSum g n := by
  induction n with
  | zero => simp [densePrefixSum]
  | succ n ih =>
      rw [densePrefixSum, densePrefixSum,
        ih (fun i hi => h i (by omega)), h n (by omega)]

theorem densePrefixSum_add (f g : Nat -> Nat) (n : Nat) :
    densePrefixSum (fun i => f i + g i) n =
      densePrefixSum f n + densePrefixSum g n := by
  induction n with
  | zero => simp [densePrefixSum]
  | succ n ih =>
      rw [densePrefixSum, densePrefixSum, densePrefixSum, ih]
      omega

/-- Prefix cancellation after the zero-inversion PiZero identity.

For dense blockers `b_i = 2*i`, the capacity of earlier column `h+1` is

`2*(h+1) - c_(h+1) - 1 = kappa_(h+1)`.

Thus aggregate capacity through rank `m+1` cancels every earlier load and
forces the newest one to vanish. -/
theorem dense_prefix_aggregate_cancellation
    (m : Nat) (c kappa : Nat -> Nat)
    (hPiZero : forall i, i < m + 1 ->
      c (i + 1) + kappa (i + 1) = 2 * (i + 1) - 1)
    (hAggregate :
      densePrefixSum (fun i => kappa (i + 1)) (m + 1) <=
        densePrefixSum
          (fun h => 2 * (h + 1) - c (h + 1) - 1) m) :
    kappa (m + 1) = 0 /\
      c (m + 1) = 2 * (m + 1) - 1 := by
  have hCapacity : forall h, h < m ->
      2 * (h + 1) - c (h + 1) - 1 = kappa (h + 1) := by
    intro h hh
    have hPi := hPiZero h (by omega)
    omega
  have hRewrite :
      densePrefixSum
          (fun h => 2 * (h + 1) - c (h + 1) - 1) m =
        densePrefixSum (fun h => kappa (h + 1)) m :=
    densePrefixSum_congr hCapacity
  rw [hRewrite, densePrefixSum] at hAggregate
  have hk : kappa (m + 1) = 0 := by omega
  refine ⟨hk, ?_⟩
  have hPi := hPiZero m (by omega)
  omega

/-- Exact residual when the PiZero inversion term is retained.

If `ell_i` counts the earlier freezes inverted across rank `i`, aggregate
capacity gives only

`kappa_(m+1) <= sum_{h<m} ell_(h+1)`.

Consequently the cancellation proof genuinely needs FreezeOrder (or another
theorem killing the inversion budget); PiZero plus aggregate capacity alone
does not force maximal freezes. -/
theorem dense_prefix_aggregate_with_inversions
    (m : Nat) (c ell kappa : Nat -> Nat)
    (hPiZero : forall i, i < m + 1 ->
      c (i + 1) + ell (i + 1) + kappa (i + 1) =
        2 * (i + 1) - 1)
    (hAggregate :
      densePrefixSum (fun i => kappa (i + 1)) (m + 1) <=
        densePrefixSum
          (fun h => 2 * (h + 1) - c (h + 1) - 1) m) :
    kappa (m + 1) <=
      densePrefixSum (fun h => ell (h + 1)) m := by
  have hCapacity : forall h, h < m ->
      2 * (h + 1) - c (h + 1) - 1 =
        ell (h + 1) + kappa (h + 1) := by
    intro h hh
    have hPi := hPiZero h (by omega)
    omega
  have hRewrite :
      densePrefixSum
          (fun h => 2 * (h + 1) - c (h + 1) - 1) m =
        densePrefixSum
          (fun h => ell (h + 1) + kappa (h + 1)) m :=
    densePrefixSum_congr hCapacity
  rw [hRewrite,
    densePrefixSum_add (fun h => ell (h + 1)) (fun h => kappa (h + 1)),
    densePrefixSum] at hAggregate
  omega

/-- Rank two already kills the dense `b_i=2*i` interface once the banked
gap-one theorem is admitted.

The aggregate prefix inequality at `m=1` forces `c_2=3`. If blocker four
freezes in that column, then `fb 3 = 4`, contradicting `GapOneKill`.
-/
theorem dense_rank_two_breaks_gapOne
    (fb c kappa : Nat -> Nat)
    (hPiZero : forall i, i < 2 ->
      c (i + 1) + kappa (i + 1) = 2 * (i + 1) - 1)
    (hAggregate :
      densePrefixSum (fun i => kappa (i + 1)) 2 <=
        densePrefixSum
          (fun h => 2 * (h + 1) - c (h + 1) - 1) 1)
    (hFreezeTwo : fb (c 2) = 4)
    (hGapOne : R132OldLossTerminalCellKill.GapOneKill fb) : False := by
  have hForced := dense_prefix_aggregate_cancellation 1 c kappa
    (by
      intro i hi
      exact hPiZero i (by omega))
    (by simpa using hAggregate)
  have hcTwo : c 2 = 3 := by
    have h := hForced.2
    omega
  have hfbThree : fb 3 = 4 := by simpa [hcTwo] using hFreezeTwo
  exact (hGapOne 3 (by omega)) (by simpa using hfbThree)

#print axioms densePrefixSum_congr
#print axioms densePrefixSum_add
#print axioms dense_prefix_aggregate_cancellation
#print axioms dense_prefix_aggregate_with_inversions
#print axioms dense_rank_two_breaks_gapOne

end ChompLean
