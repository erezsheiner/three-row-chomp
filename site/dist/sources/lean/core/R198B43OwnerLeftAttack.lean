import R198B43PlusTwoDiagonalRoute
import R181ActualTerminalBlockerOrderedHall
import R200FloorPlusFromDiagDoubleSlack

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R198: attack on the B43 `u+2` owner-left frontier

The diagonal-owner and terminal-Hall bank gets close to the empirical
source law, but leaves one genuinely spatial inequality.

* The unconditional diagonal lower envelope puts every owner of `u+2`
  before the second-successor row once `u >= 83`.
* Exact row-start order puts the skipped host strictly left of the target
  freeze, and terminal Hall gives the usual scalar freeze-column cap.
* These facts, even together with Floor+, AFloor, exact midpoint arithmetic,
  and both high-cell source-capacity inequalities, do not imply `a <= x`.

The missing numerical content can be stated sharply.  The unconditional
diagonal envelope closes owner-left from `2*u <= 3*x`.  If the stronger
paper-bank Floor+ theorem is supplied, the slightly weaker margin
`2*u <= 3*x+3` is enough.
-/

/-- Empirical host-position floor on the high first-successor packet. -/
def B43FirstSuccessorTwoThirdHostFloorFrom83 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    2 * u <= 3 * x

/-- Weaker host margin sufficient when the sharp diagonal Floor+ bound is
available. -/
def B43FirstSuccessorFloorPlusHostMarginFrom83 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    2 * u <= 3 * x + 3

/-- The unconditional `3/2` diagonal lower envelope converts the
two-thirds host floor directly into the desired owner-left inequality. -/
theorem gameF_plusTwo_diagonal_owner_le_of_twoThirdHostFloor
    {u x a : Nat}
    (hhostFloor : 2 * u <= 3 * x)
    (howner : gameF a a = u + 2) :
    a <= x := by
  have henv := gameF_overlap_env_lower_bound a
  rw [howner] at henv
  omega

/-- Consequently the cache-facing two-thirds host floor closes the exact
high-target owner-left atom. -/
theorem b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_twoThirdHostFloor
    (hfloor : B43FirstSuccessorTwoThirdHostFloorFrom83) :
    B43FirstSuccessorPlusTwoOwnerLeftFrom83 := by
  intro u L c x m a hu83 hpacket howner
  exact gameF_plusTwo_diagonal_owner_le_of_twoThirdHostFloor
    (hfloor hu83 hpacket) howner

/-- Combined high-target source law: B46 and NoTriple provide the diagonal
owner, while the two-thirds host floor puts that owner inside the prefix. -/
theorem b43FirstSuccessorPastDiagonalFrom83_of_skippedBlocker_noTriple_twoThirdHostFloor
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    (hfloor : B43FirstSuccessorTwoThirdHostFloorFrom83) :
    B43FirstSuccessorPastDiagonalFrom83 :=
  b43FirstSuccessorPastDiagonalFrom83_of_skippedBlocker_noTriple_ownerLeft
    hblocker hnoTriple
    (b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_twoThirdHostFloor hfloor)

/-- Pointwise Floor+ route.  Its additive three units are exact for this
simple arithmetic implication. -/
theorem gameF_plusTwo_diagonal_owner_le_of_floorPlusHostMargin
    {u x a : Nat}
    (hFloorPlus : 3 * a + 5 <= 2 * (u + 2))
    (hhostMargin : 2 * u <= 3 * x + 3) :
    a <= x := by
  omega

/-- Conditional actual-game wrapper for the Floor+ route.  Small owners
are impossible at `u >= 83` by diagonal source capacity, so the bank-domain
tail `a >= 16` is automatic. -/
theorem b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_diagDoubleSlack_hostMargin
    (hDDS : ActualDiagDoubleSlack)
    (hmargin : B43FirstSuccessorFloorPlusHostMarginFrom83) :
    B43FirstSuccessorPlusTwoOwnerLeftFrom83 := by
  intro u L c x m a hu83 hpacket howner
  have ha16 : 16 <= a := by
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel a
    change gameF a a <= a + a + 1 at hcap
    rw [howner] at hcap
    omega
  have hFloorPlus : 3 * a + 5 <= 2 * (u + 2) :=
    gameF_FloorPlus_of_diagDoubleSlack hDDS ha16 howner
  exact gameF_plusTwo_diagonal_owner_le_of_floorPlusHostMargin
    hFloorPlus (hmargin hu83 hpacket)

/-! ## What the currently proved packet already gives -/

/-- The skipped host is strictly left of the target freeze.  This is the
full contribution of exact row-start host order to the owner-left attack. -/
theorem b43_firstSuccessorPacket_host_left_target_freeze
    {u L c x m : Nat}
    (hpacket : B43FirstSuccessorPacket u L c x m) :
    x < c := by
  rcases hpacket with
    ⟨hu, hLpos, hL20, hcu, hfreeze, hxHorizon,
      hmSkipped, hmL, hhost, hfirst⟩
  have hrowOrder : u - L <= u - m := Nat.sub_le_sub_left hmL u
  have hxHost : x <= u - m := Nat.le_trans hxHorizon hrowOrder
  have hmpos : 0 < m := by
    unfold B43LocalSkippedLag at hmSkipped
    omega
  have hxHostStrict : x < u - m := by
    by_cases heq : x = u - m
    · have hdiag : gameF (u - m) (u - m) = u := by
        simpa only [heq] using hhost
      exact False.elim
        (disjoint_D_S gameRecurrenceModel
          ⟨u - m, hdiag⟩ ⟨c, hcu, hfreeze⟩)
    · omega
  rcases rowstart_host_order_exact gameRecurrenceModel
      hcu hfreeze hxHostStrict (by omega : u - m <= u) hhost with
      hbefore | hboundary
  · exact hbefore.2
  · omega

/-- Terminal Hall supplies only the target-freeze scalar cap. -/
theorem b43_firstSuccessorPacket_target_terminal_cap
    {u L c x m : Nat}
    (hpacket : B43FirstSuccessorPacket u L c x m) :
    u <= 2 * c + 1 := by
  have hcap := gameF_terminal_freeze_value_le_twice_column_plus_one
    hpacket.2.2.2.1 hpacket.2.2.2.2.1
  omega

/-- At the high threshold, the unconditional diagonal envelope already
makes the owner temporally past.  Thus `a <= x`, not `a < row`, is the sole
remaining part of the `DiagPrefix` witness. -/
theorem b43_firstSuccessor_plusTwo_owner_before_second_row
    {u L c x m a : Nat}
    (hu83 : 83 <= u)
    (hpacket : B43FirstSuccessorPacket u L c x m)
    (howner : gameF a a = u + 2) :
    a < u - m + 2 := by
  have hm20 : m <= 20 := by
    have hmL : m <= L := hpacket.2.2.2.2.2.2.2.1
    have hL20 : L <= 20 := hpacket.2.2.1
    omega
  have henv := gameF_overlap_env_lower_bound a
  rw [howner] at henv
  omega

/-! ## Arithmetic red team

The following infinite scalar family satisfies every numerical inequality
exported by the obvious proof route: packet bounds at lag twenty, exact
two-column target geometry, terminal Hall, AFloor, exact target midpoint,
the unconditional diagonal envelope, sharp Floor+, both high-cell source
capacities, and a temporally past owner.  Nevertheless `a=x+1`.

It is not a recurrence-model counterexample.  It proves that subtracting
the currently banked scalar inequalities cannot establish owner-left; a
new relational host-position theorem such as the two-thirds floor is
required.
-/
theorem b43_ownerLeft_not_forced_by_current_scalar_bounds
    (k : Nat) (hk : 28 <= k) :
    let u := 3 * k
    let L := 20
    let m := 20
    let x := 2 * k - 2
    let c := 2 * k
    let a := 2 * k - 1
    let A := k
    83 <= u /\
      0 < L /\ L <= 20 /\ m <= L /\ x <= u - L /\
      x < c /\ c = x + 2 /\ c < u /\
      u + A <= 2 * c + 1 /\
      u <= 3 * A + 2 /\
      2 * c = u + A /\
      a + 1 + (a + 1) / 2 <= u + 2 /\
      3 * a + 5 <= 2 * (u + 2) /\
      u + 2 <= 2 * a + 1 /\
      u - 1 <= (u - m) + x /\
      u <= (u - m + 1) + x /\
      a < u - m + 2 /\
      Not (a <= x) := by
  dsimp
  omega

#print axioms gameF_plusTwo_diagonal_owner_le_of_twoThirdHostFloor
#print axioms b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_twoThirdHostFloor
#print axioms b43FirstSuccessorPastDiagonalFrom83_of_skippedBlocker_noTriple_twoThirdHostFloor
#print axioms gameF_plusTwo_diagonal_owner_le_of_floorPlusHostMargin
#print axioms b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_diagDoubleSlack_hostMargin
#print axioms b43_firstSuccessorPacket_host_left_target_freeze
#print axioms b43_firstSuccessorPacket_target_terminal_cap
#print axioms b43_firstSuccessor_plusTwo_owner_before_second_row
#print axioms b43_ownerLeft_not_forced_by_current_scalar_bounds

end ChompLean
