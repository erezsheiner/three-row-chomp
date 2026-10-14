import R198B43LocalRecurrenceFrontier

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R198: the past-diagonal source behind the two-step B43 break

The cache audit of the rare one-step continuations gives a much sharper
target than the generic MEX disjunction. The proposed law is that whenever
a skipped target host continues once from `u` to `u+1`, the value `u+2`
has a diagonal owner at or to the left of the column. If supplied, this law
puts `u+2` in the `R` source of the second successor cell and excludes that
cell from emitting `u+2`. The module retains the proposed law as hypotheses.

The combined past-diagonal statement splits naturally into two prospective
lemmas: `u+2` is a diagonal value, and its unique diagonal owner lies at or
to the left of `x`.
-/

/-- The exact hypotheses at one of the rare first-successor continuations. -/
def B43FirstSuccessorPacket (u L c x m : Nat) : Prop :=
  64 <= u /\
  0 < L /\
  L <= 20 /\
  c < u /\
  gameF u c = u /\
  x <= u - L /\
  B43LocalSkippedLag m /\
  m <= L /\
  gameF (u - m) x = u /\
  gameF (u - m + 1) x = u + 1

/-- Minimal source atom suggested by all 145 one-step continuations in the
`N=16000` audit. -/
def B43FirstSuccessorPastDiagonal : Prop :=
  forall {u L c x m : Nat},
    B43FirstSuccessorPacket u L c x m ->
    DiagPrefix gameF (u - m + 2) x (u + 2)

/-- First half of the prospective proof: the next-next target is diagonal. -/
def B43FirstSuccessorPlusTwoDiagonal : Prop :=
  forall {u L c x m : Nat},
    B43FirstSuccessorPacket u L c x m ->
    D gameF (u + 2)

/-- Second half: the diagonal owner of `u+2` is already visible through
column `x`. -/
def B43FirstSuccessorPlusTwoOwnerLeft : Prop :=
  forall {u L c x m a : Nat},
    B43FirstSuccessorPacket u L c x m ->
    gameF a a = u + 2 ->
    a <= x

/-- Diagonal classification plus the owner bound gives the exact source
atom. -/
theorem b43FirstSuccessorPastDiagonal_of_plusTwoDiagonal_ownerLeft
    (hdiag : B43FirstSuccessorPlusTwoDiagonal)
    (hleft : B43FirstSuccessorPlusTwoOwnerLeft) :
    B43FirstSuccessorPastDiagonal := by
  intro u L c x m hpacket
  rcases hdiag hpacket with ⟨a, ha⟩
  have hax : a <= x := hleft hpacket ha
  rcases hpacket with
    ⟨_hu, _hLpos, _hL20, _hcu, _hfreeze, hx, _hmSkipped,
      hmL, _hhost, _hfirst⟩
  exact ⟨a, by omega, hax, ha⟩

/-- A past-diagonal certificate is already enough to force the local
two-step chain break. -/
theorem b43SkippedTwoStepChainBreak_of_firstSuccessorPastDiagonal
    (hpast : B43FirstSuccessorPastDiagonal) :
    B43SkippedTwoStepChainBreak := by
  intro u L c x m hu hLpos hL20 hcu hfreeze hxHorizon
      hmSkipped hmL hhost
  by_cases hfirst : gameF (u - m + 1) x = u + 1
  · right
    have hpacket : B43FirstSuccessorPacket u L c x m :=
      ⟨hu, hLpos, hL20, hcu, hfreeze, hxHorizon,
        hmSkipped, hmL, hhost, hfirst⟩
    have hdiag : DiagPrefix gameF (u - m + 2) x (u + 2) :=
      hpast hpacket
    have hR : R gameF (u - m + 2) x (u + 2) :=
      (R_iff_diagPrefix_or_colTail.mpr (Or.inl hdiag))
    have hB : B gameF (u - m + 2) x (u + 2) := Or.inl hR
    have hxHost : x <= u - m := by omega
    have hmLower : 3 <= m := by
      unfold B43LocalSkippedLag at hmSkipped
      omega
    have hmex :=
      gameF_second_successor_is_mex_of_first_affine_successor
        hxHost (by omega) hfirst
    intro hsecond
    have hmexTarget :
        IsMex (B gameF (u - m + 2) x) (u + 2) := by
      simpa [hsecond] using hmex
    exact hmexTarget.2.1 hB
  · exact Or.inl hfirst

/-- End-to-end B31 reverse inclusion from the past-diagonal source atom. -/
theorem b31_relevantSkippedSeat_is_candidate_of_firstSuccessorPastDiagonal
    (hpast : B43FirstSuccessorPastDiagonal)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  exact b31_relevantSkippedSeat_is_candidate_of_twoStepChainBreak
    (b43SkippedTwoStepChainBreak_of_firstSuccessorPastDiagonal hpast)
    hu hLpos hL20 hcu hfreeze hrelevant

#print axioms b43FirstSuccessorPastDiagonal_of_plusTwoDiagonal_ownerLeft
#print axioms b43SkippedTwoStepChainBreak_of_firstSuccessorPastDiagonal
#print axioms b31_relevantSkippedSeat_is_candidate_of_firstSuccessorPastDiagonal

end ChompLean
