import R195B30CandidateBridge

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R196: B30 at the depth-eight SeatCollision horizon

B26's strict SeatCollision branch is inspected at row `u-8`, whereas the
first R195 wrapper was phrased only at row `u-20`.  The recurrence core and
the fourteen proved rails work uniformly at every positive depth at most
twenty.  This file exposes that uniform statement and specializes it to
depth eight.
-/

/-- The six skipped lags, truncated at the requested depth `L`. -/
def B30SkippedSeatAtDepth (u L x : Nat) : Prop :=
  exists m,
    (m = 3 \/ m = 8 \/ m = 10 \/ m = 13 \/ m = 18 \/ m = 20) /\
    m <= L /\ gameF (u - m) x = u

/-- The physical cache-candidate interface at an arbitrary terminal depth.
It is the depth-parametric version of `B30PhysicalCacheCandidate20`. -/
def B30PhysicalCacheCandidateAtDepth (u L c x : Nat) : Prop :=
  3 <= x /\
  x < c /\
  B30FateCandidateAt (u - L) x /\
  Not (ColTail gameF (u - L) x u) /\
  x <= u - L

/-- At depth twenty the parametric candidate is exactly the R195 one. -/
theorem b30PhysicalCacheCandidateAtDepth_twenty_iff
    {u c x : Nat} :
    B30PhysicalCacheCandidateAtDepth u 20 c x <->
      B30PhysicalCacheCandidate20 u c x := by
  constructor
  · rintro ⟨hx3, hxc, hfate, hclear, hx20⟩
    exact ⟨⟨hx3, hxc, hfate, hclear⟩, hx20⟩
  · rintro ⟨⟨hx3, hxc, hfate, hclear⟩, hx20⟩
    exact ⟨hx3, hxc, hfate, hclear, hx20⟩

/-- Uniform corrected FutureSeat containment for every depth `1..20`.

The affine schedule is no longer a premise.  The semantic fate-candidate
condition excludes every stabilized rail column, and the recurrence leaves
only a skipped lag no larger than `L`, or a freeze in the terminal strip. -/
theorem gameF_b30PhysicalCacheCandidateAtDepth_futureSkipped_or_nearFreeze
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hcandidate : B30PhysicalCacheCandidateAtDepth u L c x) :
    B30SkippedSeatAtDepth u L x \/
      NearFreezeSeatBetween u (u - L) x := by
  rcases hcandidate with
    ⟨_hx3, hxc, hfate, hclear, hxL⟩
  have hlive : ColumnLiveBelow (u - L + 1) x :=
    b30FateCandidateAt_columnLiveBelow hfate
  have havoid : AvoidsAffineRail20 x :=
    avoidsAffineRail20_of_b30FateCandidateAt (by omega) hfate
  rcases gameF_futureLagSeatContainment_core
      (r := u - L) (by omega) hcu hfreeze hxc hlive hclear with
      hfuture | hnear
  · left
    rcases hfuture with ⟨m, hmpos, hmL, hmhost⟩
    have hm20 : m <= 20 := by omega
    by_cases hskipped :
        m = 3 \/ m = 8 \/ m = 10 \/ m = 13 \/ m = 18 \/ m = 20
    · exact ⟨m, hskipped, by omega, hmhost⟩
    · have hmRealized : RealizedLag20 m := by
        unfold RealizedLag20
        omega
      have hrail :
          gameF (u - m) (realizedRailCol20 m) = u :=
        gameF_affineRails20At_of_ge_sixtythree (by omega) m hmRealized
      have hxrow : x <= u - m := by omega
      have hrailrow : realizedRailCol20 m <= u - m := by
        have h31 := realizedLag20_railCol_le_thirtyOne hmRealized
        omega
      have hxeq : x = realizedRailCol20 m :=
        gameRecurrenceModel.fixed_q_injective
          hxrow hrailrow (hmhost.trans hrail.symm)
      exact False.elim (havoid m hmRealized hxeq)
  · exact Or.inr hnear

/-- The six realized affine lags below the depth-eight horizon. -/
def RealizedLag8 (m : Nat) : Prop :=
  m = 1 \/ m = 2 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7

/-- All depth-eight rail columns are affine already by row 19. -/
theorem realizedLag8Rail_affine_settled_by_nineteen
    {m : Nat} (hm : RealizedLag8 m) :
    forall q, 19 <= q ->
      gameF q (realizedRailCol20 m) = q + m := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
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

/-- A fate candidate at row at least 19 cannot be any depth-eight rail. -/
theorem b30FateCandidateAt_avoids_realizedLag8Rail
    {r x m : Nat}
    (hr : 19 <= r)
    (hfate : B30FateCandidateAt r x)
    (hm : RealizedLag8 m) :
    x ≠ realizedRailCol20 m := by
  intro hxm
  have hmpos : 0 < m := by
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hrail := realizedLag8Rail_affine_settled_by_nineteen hm
  rcases hfate with hmortal | himmortal
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

/-- Exact depth-eight frontier used by the strict SeatCollision branch.
All six realized affine lags `1,2,4,5,6,7` have disappeared; only the two
non-affine target landings and a genuine near freeze remain. -/
theorem gameF_b30PhysicalCacheCandidateAtDepth_eight_frontier
    {u c x : Nat}
    (hu : 27 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hcandidate : B30PhysicalCacheCandidateAtDepth u 8 c x) :
    gameF (u - 3) x = u \/
    gameF (u - 8) x = u \/
    NearFreezeSeatBetween u (u - 8) x := by
  rcases hcandidate with
    ⟨_hx3, hxc, hfate, hclear, hx8⟩
  have hlive : ColumnLiveBelow (u - 8 + 1) x :=
    b30FateCandidateAt_columnLiveBelow hfate
  rcases gameF_futureLagSeatContainment_core
      (r := u - 8) (by omega) hcu hfreeze hxc hlive hclear with
      hfuture | hnear
  · rcases hfuture with ⟨m, hmpos, hm8, hmhost⟩
    by_cases hm3 : m = 3
    · left
      simpa [hm3] using hmhost
    by_cases hm8eq : m = 8
    · right; left
      simpa [hm8eq] using hmhost
    have hmRealized : RealizedLag8 m := by
      unfold RealizedLag8
      omega
    have havoid : x ≠ realizedRailCol20 m :=
      b30FateCandidateAt_avoids_realizedLag8Rail
        (by omega) hfate hmRealized
    have hrail : gameF (u - m) (realizedRailCol20 m) = u := by
      have haffine :=
        realizedLag8Rail_affine_settled_by_nineteen hmRealized
          (u - m) (by omega)
      omega
    have hcol11 : realizedRailCol20 m <= 11 := by
      rcases hmRealized with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    have hxeq : x = realizedRailCol20 m :=
      gameRecurrenceModel.fixed_q_injective
        (by omega) (by omega) (hmhost.trans hrail.symm)
    exact False.elim (havoid hxeq)
  · exact Or.inr (Or.inr hnear)

/-- Elimination form for B26: once its two self-reference landings and its
near-freeze residue are discharged, the strict SeatCollision candidate set
is empty.  No density, midpoint pin, or abstract rail schedule remains. -/
theorem no_b30PhysicalCacheCandidateAtDepth_eight_of_no_residual
    {u c x : Nat}
    (hu : 27 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hno3 : gameF (u - 3) x ≠ u)
    (hno8 : gameF (u - 8) x ≠ u)
    (hnoNear : Not (NearFreezeSeatBetween u (u - 8) x)) :
    Not (B30PhysicalCacheCandidateAtDepth u 8 c x) := by
  intro hcandidate
  rcases gameF_b30PhysicalCacheCandidateAtDepth_eight_frontier
      hu hcu hfreeze hcandidate with h3 | h8 | hnear
  · exact hno3 h3
  · exact hno8 h8
  · exact hnoNear hnear

/-! The other audited depths are now packaged too. -/

theorem gameF_b30PhysicalCacheCandidateAtDepth_thirteen_frontier
    {u c x : Nat}
    (hu : 64 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hcandidate : B30PhysicalCacheCandidateAtDepth u 13 c x) :
    gameF (u - 3) x = u \/
    gameF (u - 8) x = u \/
    gameF (u - 10) x = u \/
    gameF (u - 13) x = u \/
    NearFreezeSeatBetween u (u - 13) x := by
  rcases gameF_b30PhysicalCacheCandidateAtDepth_futureSkipped_or_nearFreeze
      hu (by omega) (by omega) hcu hfreeze hcandidate with hseat | hnear
  · rcases hseat with ⟨m, hm, hm13, hmhost⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hmhost
    · exact Or.inr (Or.inl hmhost)
    · exact Or.inr (Or.inr (Or.inl hmhost))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hmhost)))
    · omega
    · omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr hnear)))

theorem gameF_b30PhysicalCacheCandidateAtDepth_eighteen_frontier
    {u c x : Nat}
    (hu : 64 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hcandidate : B30PhysicalCacheCandidateAtDepth u 18 c x) :
    gameF (u - 3) x = u \/
    gameF (u - 8) x = u \/
    gameF (u - 10) x = u \/
    gameF (u - 13) x = u \/
    gameF (u - 18) x = u \/
    NearFreezeSeatBetween u (u - 18) x := by
  rcases gameF_b30PhysicalCacheCandidateAtDepth_futureSkipped_or_nearFreeze
      hu (by omega) (by omega) hcu hfreeze hcandidate with hseat | hnear
  · rcases hseat with ⟨m, hm, hm18, hmhost⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hmhost
    · exact Or.inr (Or.inl hmhost)
    · exact Or.inr (Or.inr (Or.inl hmhost))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hmhost)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmhost))))
    · omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hnear))))

#print axioms gameF_b30PhysicalCacheCandidateAtDepth_futureSkipped_or_nearFreeze
#print axioms gameF_b30PhysicalCacheCandidateAtDepth_eight_frontier
#print axioms no_b30PhysicalCacheCandidateAtDepth_eight_of_no_residual
#print axioms gameF_b30PhysicalCacheCandidateAtDepth_thirteen_frontier
#print axioms gameF_b30PhysicalCacheCandidateAtDepth_eighteen_frontier

end ChompLean
