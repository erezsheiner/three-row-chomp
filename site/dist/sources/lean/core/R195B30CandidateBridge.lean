import R195B30FutureSeatClosure

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R195 B30: candidate-to-nonrail bridge

The cache candidate used two different notions of being alive past a row:

* a mortal column has not yet reached its row-start freeze; and
* an immortal column has not yet reached its eventual affine tail.

Those notions were not previously packaged as a Lean predicate.  The
definitions below state exactly the part of that candidate test needed for
the finite B30 rail exclusion.  They deliberately do not build a computable
least stabilization time: `Not (ColumnAffineSettledBy r x)` is the direct
propositional form of `sigma(x) > r`.
-/

/-- A column is mortal when some row-start value eventually freezes in it. -/
def B30ColumnMortal (x : Nat) : Prop :=
  exists w, x < w /\ gameF w x = w

/-- From row `r` onward, the column is an affine tail with some offset. -/
def ColumnAffineSettledBy (r x : Nat) : Prop :=
  exists k, forall q, r <= q -> gameF q x = q + k

/-- The mortal/immortal part of the empirical B30 candidate test.

For a mortal column this says its freeze is still in the future.  For an
immortal column it says its affine stabilization is still in the future. -/
def B30FateCandidateAt (r x : Nat) : Prop :=
  (B30ColumnMortal x /\ ColumnLiveBelow (r + 1) x) \/
  (Not (B30ColumnMortal x) /\ Not (ColumnAffineSettledBy r x))

/-- Full depth-twenty cache candidate, apart from the separately supplied
fact that `c` is the freeze column of `u`. -/
def B30CacheCandidate20 (u c x : Nat) : Prop :=
  3 <= x /\
  x < c /\
  B30FateCandidateAt (u - 20) x /\
  Not (ColTail gameF (u - 20) x u)

/-- The physical depth-twenty wrapper.  The cache audit found that every
candidate above also satisfied this row-domain guard, but the guard is kept
explicit because it is a separate interface requirement of the recurrence
theorem. -/
def B30PhysicalCacheCandidate20 (u c x : Nat) : Prop :=
  B30CacheCandidate20 u c x /\ x <= u - 20

/-- An immortal column is live below every row: a row-start freeze in the
column would itself witness mortality. -/
theorem columnLiveBelow_of_not_b30ColumnMortal
    {v x : Nat}
    (himmortal : Not (B30ColumnMortal x)) :
    ColumnLiveBelow v x := by
  intro w hxw hwv hwfreeze
  exact himmortal ⟨w, hxw, hwfreeze⟩

/-- Both arms of the fate candidate supply the exact `ColumnLiveBelow`
premise used by the R190 containment core. -/
theorem b30FateCandidateAt_columnLiveBelow
    {r x : Nat}
    (hcandidate : B30FateCandidateAt r x) :
    ColumnLiveBelow (r + 1) x := by
  rcases hcandidate with hmortal | himmortal
  · exact hmortal.2
  · exact columnLiveBelow_of_not_b30ColumnMortal himmortal.1

/-- Every one of the fourteen realized rail columns has entered its affine
tail by row 44.  This is the formal counterpart of the cache receipt that
all relevant immortal columns stabilize by that row. -/
theorem realizedRail20_affine_settled_by_fortyFour
    {m : Nat} (hm : RealizedLag20 m) :
    forall q, 44 <= q ->
      gameF q (realizedRailCol20 m) = q + m := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [realizedRailCol20]
  · intro q hq
    rw [gameF_col0]
  · intro q hq
    rw [gameF_col2_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col5_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col7_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col9_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col11_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col14_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col17_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col19_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col22_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col24_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col26_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col28_rail (q := q) (by omega)]
  · intro q hq
    rw [gameF_col31_rail (q := q) (by omega)]

/-- Once the comparison row is at least 44, either arm of the exact fate
candidate test excludes every stabilized affine rail column. -/
theorem avoidsAffineRail20_of_b30FateCandidateAt
    {r x : Nat}
    (hr : 44 <= r)
    (hcandidate : B30FateCandidateAt r x) :
    AvoidsAffineRail20 x := by
  intro m hm hxm
  have hmpos : 0 < m := by
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hrail := realizedRail20_affine_settled_by_fortyFour hm
  rcases hcandidate with hmortal | himmortal
  · rcases hmortal with ⟨⟨w, hxw, hwfreeze⟩, hlive⟩
    have hrw : r < w := by
      apply Nat.lt_of_not_ge
      intro hwr
      exact hlive w hxw (by omega) hwfreeze
    have hwaffine : gameF w x = w + m := by
      rw [hxm]
      exact hrail w (by omega)
    omega
  · rcases himmortal with ⟨_himmortal, hnotSettled⟩
    apply hnotSettled
    refine ⟨m, ?_⟩
    intro q hrq
    rw [hxm]
    exact hrail q (by omega)

/-- At depth twenty the cache-candidate condition itself supplies the last
candidate-side premise of the R195 B30 closure.  The threshold is `u >= 64`
because its comparison row is `u-20`, and column 31 stabilizes at row 44. -/
theorem b30CacheCandidate20_avoidsAffineRail20
    {u c x : Nat}
    (hu : 64 <= u)
    (hcandidate : B30CacheCandidate20 u c x) :
    AvoidsAffineRail20 x := by
  exact avoidsAffineRail20_of_b30FateCandidateAt
    (by omega) hcandidate.2.2.1

/-- End-to-end corrected B30 at depth twenty.  The last conjunct of
`B30CacheCandidate20` is literally R190's target-clear interface
`Not (ColTail gameF (u-20) x u)`.  The physical wrapper supplies the only
additional row-domain guard. -/
theorem gameF_b30PhysicalCacheCandidate20_futureSkipped_or_nearFreeze
    {u c x : Nat}
    (hu : 64 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hcandidate : B30PhysicalCacheCandidate20 u c x) :
    SkippedSeat20 u x \/ NearFreezeSeatBetween u (u - 20) x := by
  rcases hcandidate with ⟨⟨_hx3, hxc, hfate, hclear⟩, hx20⟩
  have halive : ColumnLiveBelow (u - 20 + 1) x :=
    b30FateCandidateAt_columnLiveBelow hfate
  have havoid : AvoidsAffineRail20 x :=
    avoidsAffineRail20_of_b30FateCandidateAt (by omega) hfate
  exact gameF_futureSkippedSeat20_or_nearFreeze_of_avoidsAffineRail20
    (by omega) hcu hfreeze hxc hx20 halive hclear havoid

#print axioms realizedRail20_affine_settled_by_fortyFour
#print axioms avoidsAffineRail20_of_b30FateCandidateAt
#print axioms b30CacheCandidate20_avoidsAffineRail20
#print axioms columnLiveBelow_of_not_b30ColumnMortal
#print axioms b30FateCandidateAt_columnLiveBelow
#print axioms gameF_b30PhysicalCacheCandidate20_futureSkipped_or_nearFreeze

end ChompLean
