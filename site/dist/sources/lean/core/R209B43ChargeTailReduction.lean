import R205B43BlockerChargeMargin

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R209: tail reduction of the B43 blocker charge

The blocker-charge atom splits at target 173 into one global rank-slack law,
one uniform six-column packet gap, and a finite target interval.  In the
tail, the arithmetic is exact:

`c-x <= 6  ->  6*(c-x)+3 <= 39`,

so `u+39 <= 3*A(u-1)` supplies the desired charge.

The finite interval has a still sharper cache normal form: every packet is
at target 126, its freeze gap is one or four, and `A(125)=51`.  These facts
imply the finite charge directly; they are exposed only as certificate
interfaces and are not asserted in this file.
-/

/-! ## Tail and finite-base interfaces -/

/-- Global rank slack sufficient for every target from 173 onward. -/
def GameFBlockerRankSlack39From173 : Prop :=
  forall {u : Nat},
    173 <= u ->
    u + 39 <= 3 * gameFBlockerCountThrough (u - 1)

/-- Uniform packet geometry seen in the cache. -/
def B43FirstSuccessorFreezeGapAtMostSixFrom83 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    B43FirstSuccessorPacket u L c x m ->
    c - x <= 6

/-- Exact finite charge left below the tail threshold. -/
def B43FirstSuccessorBlockerCharge83To172 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    u < 173 ->
    B43FirstSuccessorPacket u L c x m ->
    u + 6 * (c - x) + 3 <=
      3 * gameFBlockerCountThrough (u - 1)

/-- The three interfaces give the original all-target blocker-charge atom. -/
theorem b43FirstSuccessorBlockerChargeFrom83_of_rankSlack39_gapSix_finite
    (hrank : GameFBlockerRankSlack39From173)
    (hgap : B43FirstSuccessorFreezeGapAtMostSixFrom83)
    (hfinite : B43FirstSuccessorBlockerCharge83To172) :
    B43FirstSuccessorBlockerChargeFrom83 := by
  intro u L c x m hu83 hpacket
  by_cases hu173 : 173 <= u
  . have hrank0 := hrank hu173
    have hgap0 := hgap hu83 hpacket
    omega
  . exact hfinite hu83 (by omega) hpacket

/-- Compact package for the primary tail reduction. -/
def B43BlockerChargeTailPackage : Prop :=
  GameFBlockerRankSlack39From173 /\
    B43FirstSuccessorFreezeGapAtMostSixFrom83 /\
    B43FirstSuccessorBlockerCharge83To172

theorem b43FirstSuccessorBlockerChargeFrom83_of_tailPackage
    (hpackage : B43BlockerChargeTailPackage) :
    B43FirstSuccessorBlockerChargeFrom83 := by
  rcases hpackage with ⟨hrank, hgap, hfinite⟩
  exact
    b43FirstSuccessorBlockerChargeFrom83_of_rankSlack39_gapSix_finite
      hrank hgap hfinite

/-! ## Sharper certificate interface for targets 83--172 -/

/-- Cache normal form for the finite packet interval. -/
def B43FirstSuccessorBase126GapClassification83To172 : Prop :=
  forall {u L c x m : Nat},
    83 <= u ->
    u < 173 ->
    B43FirstSuccessorPacket u L c x m ->
    u = 126 /\ (c - x = 1 \/ c - x = 4)

/-- The single blocker-rank receipt needed by that normal form. -/
def GameFBlockerCountThrough125Eq51 : Prop :=
  gameFBlockerCountThrough 125 = 51

/-- Target 126, gaps one or four, and `A(125)=51` prove the entire finite
charge interval. -/
theorem b43FirstSuccessorBlockerCharge83To172_of_base126Gap_rank125
    (hclass : B43FirstSuccessorBase126GapClassification83To172)
    (hrank125 : GameFBlockerCountThrough125Eq51) :
    B43FirstSuccessorBlockerCharge83To172 := by
  intro u L c x m hu83 hu173 hpacket
  rcases hclass hu83 hu173 hpacket with ⟨hu126, hgap⟩
  subst u
  unfold GameFBlockerCountThrough125Eq51 at hrank125
  have hindex : 126 - 1 = 125 := by omega
  rw [hindex, hrank125]
  rcases hgap with hgap | hgap <;> omega

/-- Sharper four-item package replacing the opaque finite charge by its
one-target certificate. -/
def B43BlockerChargeTail126Package : Prop :=
  GameFBlockerRankSlack39From173 /\
    B43FirstSuccessorFreezeGapAtMostSixFrom83 /\
    B43FirstSuccessorBase126GapClassification83To172 /\
    GameFBlockerCountThrough125Eq51

theorem b43FirstSuccessorBlockerChargeFrom83_of_tail126Package
    (hpackage : B43BlockerChargeTail126Package) :
    B43FirstSuccessorBlockerChargeFrom83 := by
  rcases hpackage with ⟨hrank, hgap, hclass, hrank125⟩
  exact
    b43FirstSuccessorBlockerChargeFrom83_of_rankSlack39_gapSix_finite
      hrank hgap
      (b43FirstSuccessorBlockerCharge83To172_of_base126Gap_rank125
        hclass hrank125)

#print axioms b43FirstSuccessorBlockerChargeFrom83_of_rankSlack39_gapSix_finite
#print axioms b43FirstSuccessorBlockerChargeFrom83_of_tailPackage
#print axioms b43FirstSuccessorBlockerCharge83To172_of_base126Gap_rank125
#print axioms b43FirstSuccessorBlockerChargeFrom83_of_tail126Package

end ChompLean
