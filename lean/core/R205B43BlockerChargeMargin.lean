import R201DiagDoubleSlackCeilingChain

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R205: blocker-charge reduction of the B43 host margin

Two history laws extracted from the cache imply the strong two-thirds host
floor needed by the B43 packet-local route.

Let `A = gameFBlockerCountThrough (u-1)`.  The laws are

* `u + 6*(c-x) + 3 <= 3*A`;
* `actualBlockerMidpoint u <= c`.

After unfolding `actualBlockerMidpoint` and `countMidpoint`, the second law
says `(u+A)/2 <= c`, hence `u+A <= 2*c+1`.  Combining this with the charge
law and the packet consequence `x <= c` cancels the freeze column and gives
`2*u <= 3*x`.
-/

/-! ## The two history atoms -/

/-- Cache-mined blocker-charge inequality at a high B43 first-successor
packet. -/
def B43FirstSuccessorBlockerChargeFrom83 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    u + 6 * (c - x) + 3 <=
      3 * gameFBlockerCountThrough (u - 1)

/-- Cache-mined history placement: the actual blocker midpoint of the
target lies at or left of its freeze column. -/
def B43FirstSuccessorBlockerMidpointLeFreezeFrom83 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    actualBlockerMidpoint u <= c

/-! ## Exact arithmetic bridge -/

/-- Abstract arithmetic core.  This spelling exposes the only use of
division and makes the cancellation of `c-x` explicit through `x <= c`. -/
theorem twoThirdHostFloor_of_blockerCharge_midpoint
    {u c x A : Nat}
    (hxc : x <= c)
    (hcharge : u + 6 * (c - x) + 3 <= 3 * A)
    (hmidpoint : (u + A) / 2 <= c) :
    2 * u <= 3 * x := by
  omega

/-- The two history atoms imply the strong cache-facing host floor on every
high first-successor packet. -/
theorem b43FirstSuccessorTwoThirdHostFloorFrom83_of_blockerCharge_midpoint
    (hcharge : B43FirstSuccessorBlockerChargeFrom83)
    (hmidpoint : B43FirstSuccessorBlockerMidpointLeFreezeFrom83) :
    B43FirstSuccessorTwoThirdHostFloorFrom83 := by
  intro u L c x m hu83 hpacket
  have hxc : x <= c :=
    Nat.le_of_lt (b43_firstSuccessorPacket_host_left_target_freeze hpacket)
  have hcharge0 := hcharge hu83 hpacket
  have hmidpoint0 := hmidpoint hu83 hpacket
  unfold actualBlockerMidpoint countMidpoint at hmidpoint0
  exact twoThirdHostFloor_of_blockerCharge_midpoint
    hxc hcharge0 hmidpoint0

/-! ## Consequence for the Floor+ margin route -/

/-- The strong two-thirds floor trivially supplies the three-unit Floor+
host margin. -/
theorem b43FirstSuccessorFloorPlusHostMarginFrom83_of_twoThirdHostFloor
    (hfloor : B43FirstSuccessorTwoThirdHostFloorFrom83) :
    B43FirstSuccessorFloorPlusHostMarginFrom83 := by
  intro u L c x m hu83 hpacket
  have hstrong := hfloor hu83 hpacket
  omega

/-- End-to-end reduction of the Floor+ host margin to the two cache-mined
history atoms. -/
theorem b43FirstSuccessorFloorPlusHostMarginFrom83_of_blockerCharge_midpoint
    (hcharge : B43FirstSuccessorBlockerChargeFrom83)
    (hmidpoint : B43FirstSuccessorBlockerMidpointLeFreezeFrom83) :
    B43FirstSuccessorFloorPlusHostMarginFrom83 :=
  b43FirstSuccessorFloorPlusHostMarginFrom83_of_twoThirdHostFloor
    (b43FirstSuccessorTwoThirdHostFloorFrom83_of_blockerCharge_midpoint
      hcharge hmidpoint)

/-- Compact package for the new history route. -/
def B43BlockerChargeMarginHistory : Prop :=
  B43FirstSuccessorBlockerChargeFrom83 /\
    B43FirstSuccessorBlockerMidpointLeFreezeFrom83

theorem b43FirstSuccessorTwoThirdHostFloorFrom83_of_blockerChargeHistory
    (hhistory : B43BlockerChargeMarginHistory) :
    B43FirstSuccessorTwoThirdHostFloorFrom83 := by
  rcases hhistory with ⟨hcharge, hmidpoint⟩
  exact
    b43FirstSuccessorTwoThirdHostFloorFrom83_of_blockerCharge_midpoint
      hcharge hmidpoint

theorem b43FirstSuccessorFloorPlusHostMarginFrom83_of_blockerChargeHistory
    (hhistory : B43BlockerChargeMarginHistory) :
    B43FirstSuccessorFloorPlusHostMarginFrom83 := by
  rcases hhistory with ⟨hcharge, hmidpoint⟩
  exact
    b43FirstSuccessorFloorPlusHostMarginFrom83_of_blockerCharge_midpoint
      hcharge hmidpoint

#print axioms twoThirdHostFloor_of_blockerCharge_midpoint
#print axioms b43FirstSuccessorTwoThirdHostFloorFrom83_of_blockerCharge_midpoint
#print axioms b43FirstSuccessorFloorPlusHostMarginFrom83_of_twoThirdHostFloor
#print axioms b43FirstSuccessorFloorPlusHostMarginFrom83_of_blockerCharge_midpoint
#print axioms b43FirstSuccessorTwoThirdHostFloorFrom83_of_blockerChargeHistory
#print axioms b43FirstSuccessorFloorPlusHostMarginFrom83_of_blockerChargeHistory

end ChompLean
