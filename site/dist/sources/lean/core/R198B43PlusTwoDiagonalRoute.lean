import R198B43PastDiagonalSuccessor
import R198B43SkippedBlockerNoTripleRoute

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R198: the D/S route to the `u+2` diagonal classification

Assuming `SkippedOffsetCellIsBlockerFrom64` and
`GameFNoThreeConsecutiveBlockers`, the row-64 skipped-cell classification
for a first skipped-affine continuation makes `u+1` a blocker.  The B31 target freeze makes
`u` a blocker independently.  Hence NoTriple rules out blocker status for
`u+2`, and `opening_cover` puts `u+2` in the diagonal class.

In addition to those two supplied laws, the first successor row must be
at least 64.  Since the largest skipped
lag is twenty, this condition is automatic for `u >= 83`.  It also classifies
`u+2` without assuming that the second affine successor actually occurs.

Diagonal classification alone does not place the diagonal owner inside the
cell prefix.  The remaining source-facing input is therefore exactly the
owner-left statement, recorded below in its high-target form.
-/

/-- High-target form of the prospective `u+2` diagonal law. -/
def B43FirstSuccessorPlusTwoDiagonalFrom83 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    D gameF (u + 2)

/-- Exact finite residual for upgrading the high-target law to the original
`u >= 64` packet.  Because the high argument starts at 83, the residual is
the nineteen target rows `64 <= u < 83`. -/
def B43FirstSuccessorPlusTwoDiagonalBelow83 : Prop :=
  forall {u L c x m : Nat},
    u < 83 ->
    B43FirstSuccessorPacket u L c x m ->
    D gameF (u + 2)

/-- Lag-sensitive residual: precisely the packets whose first successor row
still lies below the threshold of the skipped-cell classification. -/
def B43FirstSuccessorPlusTwoDiagonalBeforeRow64 : Prop :=
  forall {u L c x m : Nat},
    u - m + 1 < 64 ->
    B43FirstSuccessorPacket u L c x m ->
    D gameF (u + 2)

/-- The exact owner frontier remaining after the D/S argument. -/
def B43FirstSuccessorPlusTwoOwnerLeftFrom83 : Prop :=
  forall {u L c x m a : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    gameF a a = u + 2 ->
    a <= x

/-- Source-facing high-target version of the past-diagonal atom. -/
def B43FirstSuccessorPastDiagonalFrom83 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    DiagPrefix gameF (u - m + 2) x (u + 2)

/-- Pointwise D/S classification.  The sharp hypothesis is on the first
successor row, not directly on the target. -/
theorem b43_firstSuccessor_plusTwo_diagonal_of_row64_blocker_noTriple
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    {u L c x m : Nat}
    (hfirstRow64 : 64 <= u - m + 1)
    (hpacket : B43FirstSuccessorPacket u L c x m) :
    D gameF (u + 2) := by
  rcases hpacket with
    ⟨hu, hLpos, hL20, hcu, hfreeze, hxHorizon,
      hmSkipped, hmL, hhost, hfirst⟩
  have hmAffine : SkippedAffineOffset20 m :=
    b43LocalSkippedLag_iff_skippedAffineOffset20.mp hmSkipped
  have hxFirst : x <= u - m + 1 := by omega
  have hfirstAffine :
      gameF (u - m + 1) x = (u - m + 1) + m := by
    omega
  have hu1S0 : S gameF ((u - m + 1) + m) :=
    hblocker hfirstRow64 hxFirst hmAffine hfirstAffine
  have hsum : (u - m + 1) + m = u + 1 := by omega
  have hu1S : S gameF (u + 1) := by
    simpa only [hsum] using hu1S0
  have huS : S gameF u := ⟨c, hcu, hfreeze⟩
  rcases gameRecurrenceModel.opening_cover (by omega : 0 < u + 2) with
      hdiag | hrow
  · rcases hdiag with ⟨a, _ha, howner⟩
    exact ⟨a, howner⟩
  · exact False.elim (hnoTriple u ⟨huS, hu1S, hrow⟩)

/-- Uniform consequence: `u >= 83` puts the first successor row beyond 63
even for the largest skipped lag `m=20`. -/
theorem b43FirstSuccessorPlusTwoDiagonalFrom83_of_skippedBlocker_noTriple
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers) :
    B43FirstSuccessorPlusTwoDiagonalFrom83 := by
  intro u L c x m hu83 hpacket
  have hm20 : m <= 20 := by
    have hmL : m <= L := hpacket.2.2.2.2.2.2.2.1
    have hL20 : L <= 20 := hpacket.2.2.1
    omega
  exact b43_firstSuccessor_plusTwo_diagonal_of_row64_blocker_noTriple
    hblocker hnoTriple (by omega) hpacket

/-- The high law plus its exact nineteen-row residual is equivalent to the
full-threshold diagonal atom in the useful forward direction. -/
theorem b43FirstSuccessorPlusTwoDiagonal_of_high83_and_finite
    (hhigh : B43FirstSuccessorPlusTwoDiagonalFrom83)
    (hfinite : B43FirstSuccessorPlusTwoDiagonalBelow83) :
    B43FirstSuccessorPlusTwoDiagonal := by
  intro u L c x m hpacket
  by_cases hu83 : 83 <= u
  · exact hhigh hu83 hpacket
  · exact hfinite (by omega) hpacket

/-- Exact threshold split: the blocker/NoTriple argument handles every
packet whose first successor row is at least 64, leaving only the
lag-sensitive pre-64 residual. -/
theorem b43FirstSuccessorPlusTwoDiagonal_of_skippedBlocker_noTriple_residual
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    (hresidual : B43FirstSuccessorPlusTwoDiagonalBeforeRow64) :
    B43FirstSuccessorPlusTwoDiagonal := by
  intro u L c x m hpacket
  by_cases hrow64 : 64 <= u - m + 1
  · exact b43_firstSuccessor_plusTwo_diagonal_of_row64_blocker_noTriple
      hblocker hnoTriple hrow64 hpacket
  · exact hresidual (by omega) hpacket

/-- Combining the proved high diagonal classification with the still-open
owner-left frontier yields the exact high past-diagonal source. -/
theorem b43FirstSuccessorPastDiagonalFrom83_of_diagonal_ownerLeft
    (hdiag : B43FirstSuccessorPlusTwoDiagonalFrom83)
    (hleft : B43FirstSuccessorPlusTwoOwnerLeftFrom83) :
    B43FirstSuccessorPastDiagonalFrom83 := by
  intro u L c x m hu83 hpacket
  rcases hdiag hu83 hpacket with ⟨a, ha⟩
  have hax : a <= x := hleft hu83 hpacket ha
  rcases hpacket with
    ⟨_hu, _hLpos, _hL20, _hcu, _hfreeze, hxHorizon,
      _hmSkipped, hmL, _hhost, _hfirst⟩
  exact ⟨a, by omega, hax, ha⟩

/-- Under the supplied skipped-blocker and NoTriple premises, the D/S
implication is proved here. Combining it with the separately supplied
owner-left premise yields the high past-diagonal source conclusion. -/
theorem b43FirstSuccessorPastDiagonalFrom83_of_skippedBlocker_noTriple_ownerLeft
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    (hleft : B43FirstSuccessorPlusTwoOwnerLeftFrom83) :
    B43FirstSuccessorPastDiagonalFrom83 :=
  b43FirstSuccessorPastDiagonalFrom83_of_diagonal_ownerLeft
    (b43FirstSuccessorPlusTwoDiagonalFrom83_of_skippedBlocker_noTriple
      hblocker hnoTriple)
    hleft

#print axioms b43_firstSuccessor_plusTwo_diagonal_of_row64_blocker_noTriple
#print axioms b43FirstSuccessorPlusTwoDiagonalFrom83_of_skippedBlocker_noTriple
#print axioms b43FirstSuccessorPlusTwoDiagonal_of_high83_and_finite
#print axioms b43FirstSuccessorPlusTwoDiagonal_of_skippedBlocker_noTriple_residual
#print axioms b43FirstSuccessorPastDiagonalFrom83_of_diagonal_ownerLeft
#print axioms b43FirstSuccessorPastDiagonalFrom83_of_skippedBlocker_noTriple_ownerLeft

end ChompLean
