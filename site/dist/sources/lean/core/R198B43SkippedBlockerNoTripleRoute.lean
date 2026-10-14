import R198B43AffineOffsetFrontier
import R198B43LocalRecurrenceFrontier

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R198: skipped-offset blockers and the NoTriple route to B43

The cache exposes a second local route around the affine-tail obstruction.
Every observed cell of the form

`gameF q x = q + m`, with `q >= 64` and skipped
`m in {3,8,10,13,18,20}`,

has blocker output: `S gameF (q+m)`.  A settled skipped affine tail would
therefore make three consecutive values `u,u+1,u+2` blockers.  The usual
NoTriple statement rules that out.

This file deliberately keeps both ingredients as named hypotheses.  No
global NoTriple theorem, and no infinite skipped-cell classification, is
silently assumed from the finite cache.  The target freeze already supplies
the first blocker `u`; the row-64 classification is needed only at the first
successor row `u-m+1`.  Hence it settles all targets `u >= 83`, and the exact
residual base is `64 <= u < 83`.
-/

/-- The local and affine-frontier spellings use the same six offsets. -/
theorem b43LocalSkippedLag_iff_skippedAffineOffset20
    {m : Nat} :
    B43LocalSkippedLag m <-> SkippedAffineOffset20 m := by
  rfl

/-- Paper-level blocker input.  It is recorded explicitly because a global
NoTriple theorem is not currently present in the compiled Lean bank. -/
def GameFNoThreeConsecutiveBlockers : Prop :=
  forall z,
    Not (S gameF z /\ S gameF (z + 1) /\ S gameF (z + 2))

/-- Cache-discovered target-free classification.  It concerns every
physical skipped-offset cell from row 64 onward, not only B31 target seats. -/
def SkippedOffsetCellIsBlockerFrom64 : Prop :=
  forall {q x m : Nat},
    64 <= q ->
    x <= q ->
    SkippedAffineOffset20 m ->
    gameF q x = q + m ->
    S gameF (q + m)

/-- The finite residual left when the row-64 classification is used for
targets whose lag may be as large as twenty. -/
def B43FiniteBaseNoObstruction64To82 : Prop :=
  forall {u L c x : Nat},
    64 <= u ->
    u < 83 ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    B31RelevantSkippedSeatAtDepth u L x ->
    Not (B31SettledImmortalObstruction u L x)

/-- Sharper lag-sensitive finite residual.  It asks for the two-step break
only when the first successor row itself is still below 64.  Its hypotheses
force `64 <= u < 83`, but many lag/target pairs in that range are already
handled by the row-64 classification and are omitted here. -/
def B43Pre64FirstSuccessorTwoStepChainBreak : Prop :=
  forall {u L c x m : Nat},
    64 <= u ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    x <= u - L ->
    B43LocalSkippedLag m ->
    m <= L ->
    gameF (u - m) x = u ->
    u - m + 1 < 64 ->
    gameF (u - m + 1) x ≠ u + 1 \/
      gameF (u - m + 2) x ≠ u + 2

/-- Stronger finite-base atom seen in the cache: throughout the uniform
target range `64 <= u < 83`, the first successor already breaks. -/
def B43FiniteBaseFirstSuccessorBreak64To82 : Prop :=
  forall {u L c x m : Nat},
    64 <= u ->
    u < 83 ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    x <= u - L ->
    B43LocalSkippedLag m ->
    m <= L ->
    gameF (u - m) x = u ->
    gameF (u - m + 1) x ≠ u + 1

/-- The uniform low-target first-successor break supplies the sharper
lag-sensitive two-step residual. -/
theorem b43Pre64FirstSuccessorTwoStepChainBreak_of_finiteBaseFirstBreak
    (hfinite : B43FiniteBaseFirstSuccessorBreak64To82) :
    B43Pre64FirstSuccessorTwoStepChainBreak := by
  intro u L c x m hu hLpos hL20 hcu hfreeze hxHorizon
    hmSkipped hmL hhost hfirstRow
  exact Or.inl (hfinite hu (by omega) hLpos hL20 hcu hfreeze
    hxHorizon hmSkipped hmL hhost)

/-- Above target 82, the skipped-cell blocker classification and NoTriple
exclude the exact B31 obstruction.  A settled tail supplies the three
cells; the target freeze makes `u` a blocker, while `u >= 83` puts the first
successor row at or beyond 64. -/
theorem b31_no_settledImmortalObstruction_of_skippedBlocker_noTriple_high
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    {u L c x : Nat}
    (hu : 83 <= u)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    Not (B31SettledImmortalObstruction u L x) := by
  intro hbad
  rcases b31_settledImmortalObstruction_forces_two_step_chain
      (by omega : 64 <= u) hrelevant hbad with
      ⟨m, hmSkipped, hmL, _hhost, hfirst, hsecond⟩
  have hmAffine : SkippedAffineOffset20 m :=
    b43LocalSkippedLag_iff_skippedAffineOffset20.mp hmSkipped
  have hxHost : x <= u - m := by
    have hxHorizon : x <= u - L := hrelevant.2
    omega
  have hfirst' : gameF (u - m + 1) x = (u - m + 1) + m := by
    omega
  have hsecond' : gameF (u - m + 2) x = (u - m + 2) + m := by
    omega
  have hu1S0 := hblocker
    (q := u - m + 1) (x := x) (m := m)
    (by omega) (by omega) hmAffine hfirst'
  have hu2S0 := hblocker
    (q := u - m + 2) (x := x) (m := m)
    (by omega) (by omega) hmAffine hsecond'
  have hsum1 : u - m + 1 + m = u + 1 := by omega
  have hsum2 : u - m + 2 + m = u + 2 := by omega
  have huS : S gameF u := ⟨c, hcu, hfreeze⟩
  have hu1S : S gameF (u + 1) := by simpa only [hsum1] using hu1S0
  have hu2S : S gameF (u + 2) := by simpa only [hsum2] using hu2S0
  exact hnoTriple u ⟨huS, hu1S, hu2S⟩

/-- End-to-end high-target form: the same two structural inputs prove the
full B31 reverse inclusion for every `u >= 83`. -/
theorem b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_high
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    {u L c x : Nat}
    (hu : 83 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  apply (b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
    (by omega : 64 <= u) hLpos hL20 hcu hfreeze hrelevant).2
  exact
    b31_no_settledImmortalObstruction_of_skippedBlocker_noTriple_high
      hblocker hnoTriple hu hL20 hcu hfreeze hrelevant

/-- Exact threshold split.  Outside the pre-64 first-successor residual,
the blocker classification and NoTriple themselves contradict the forced
three-cell chain. -/
theorem b31_no_settledImmortalObstruction_of_skippedBlocker_noTriple_pre64Residual
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    (hresidual : B43Pre64FirstSuccessorTwoStepChainBreak)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    Not (B31SettledImmortalObstruction u L x) := by
  intro hbad
  rcases b31_settledImmortalObstruction_forces_two_step_chain
      hu hrelevant hbad with
      ⟨m, hmSkipped, hmL, hhost, hfirst, hsecond⟩
  have hxHorizon : x <= u - L := hrelevant.2
  by_cases hrow64 : 64 <= u - m + 1
  · have hmAffine : SkippedAffineOffset20 m :=
      b43LocalSkippedLag_iff_skippedAffineOffset20.mp hmSkipped
    have hxHost : x <= u - m := by omega
    have hfirst' :
        gameF (u - m + 1) x = (u - m + 1) + m := by
      omega
    have hsecond' :
        gameF (u - m + 2) x = (u - m + 2) + m := by
      omega
    have hu1S0 := hblocker
      (q := u - m + 1) (x := x) (m := m)
      hrow64 (by omega) hmAffine hfirst'
    have hu2S0 := hblocker
      (q := u - m + 2) (x := x) (m := m)
      (by omega) (by omega) hmAffine hsecond'
    have hsum1 : u - m + 1 + m = u + 1 := by omega
    have hsum2 : u - m + 2 + m = u + 2 := by omega
    have huS : S gameF u := ⟨c, hcu, hfreeze⟩
    have hu1S : S gameF (u + 1) := by
      simpa only [hsum1] using hu1S0
    have hu2S : S gameF (u + 2) := by
      simpa only [hsum2] using hu2S0
    exact hnoTriple u ⟨huS, hu1S, hu2S⟩
  · rcases hresidual hu hLpos hL20 hcu hfreeze hxHorizon
        hmSkipped hmL hhost (by omega) with hfirstBreak | hsecondBreak
    · exact hfirstBreak hfirst
    · exact hsecondBreak hsecond

/-- End-to-end B31 reverse inclusion using the exact lag-sensitive residual. -/
theorem b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_pre64Residual
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    (hresidual : B43Pre64FirstSuccessorTwoStepChainBreak)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  apply (b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
    hu hLpos hL20 hcu hfreeze hrelevant).2
  exact
    b31_no_settledImmortalObstruction_of_skippedBlocker_noTriple_pre64Residual
      hblocker hnoTriple hresidual hu hLpos hL20 hcu hfreeze hrelevant

/-- End-to-end spelling using the stronger finite law actually seen in the
low-target cache: every first successor already breaks. -/
theorem b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_finiteBaseFirstBreak
    (hblocker : SkippedOffsetCellIsBlockerFrom64)
    (hnoTriple : GameFNoThreeConsecutiveBlockers)
    (hfinite : B43FiniteBaseFirstSuccessorBreak64To82)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  exact
    b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_pre64Residual
      hblocker hnoTriple
      (b43Pre64FirstSuccessorTwoStepChainBreak_of_finiteBaseFirstBreak hfinite)
      hu hLpos hL20 hcu hfreeze hrelevant

/-- Complete closure package for this route.  The final disjunction permits
either a uniform nineteen-target base or the sharper lag-sensitive pre-64
first-successor residual. -/
def B43SkippedBlockerNoTripleClosure : Prop :=
  SkippedOffsetCellIsBlockerFrom64 /\
  GameFNoThreeConsecutiveBlockers /\
  (B43FiniteBaseNoObstruction64To82 \/
    B43Pre64FirstSuccessorTwoStepChainBreak)

/-- The row-64 classification, NoTriple, and the exact finite base together
close B31 at the original threshold `u >= 64`. -/
theorem b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple
    (hroute : B43SkippedBlockerNoTripleClosure)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  rcases hroute with ⟨hblocker, hnoTriple, hfinite | hresidual⟩
  · by_cases hu83 : 83 <= u
    · exact
        b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_high
          hblocker hnoTriple hu83 hLpos hL20 hcu hfreeze hrelevant
    · apply (b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
        hu hLpos hL20 hcu hfreeze hrelevant).2
      exact hfinite hu (by omega) hLpos hL20 hcu hfreeze hrelevant
  · exact
      b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_pre64Residual
        hblocker hnoTriple hresidual hu hLpos hL20 hcu hfreeze hrelevant

#print axioms b43LocalSkippedLag_iff_skippedAffineOffset20
#print axioms b43Pre64FirstSuccessorTwoStepChainBreak_of_finiteBaseFirstBreak
#print axioms b31_no_settledImmortalObstruction_of_skippedBlocker_noTriple_high
#print axioms b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_high
#print axioms b31_no_settledImmortalObstruction_of_skippedBlocker_noTriple_pre64Residual
#print axioms b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_pre64Residual
#print axioms b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple_finiteBaseFirstBreak
#print axioms b31_relevantSkippedSeat_is_candidate_of_skippedBlocker_noTriple

end ChompLean
