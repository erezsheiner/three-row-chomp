import R171TerminalOnlyFlipClassification
import R168PreviewAbsentHistoryCounterframe

set_option autoImplicit false

namespace ChompLean

/-!
# Terminal-only braid: the exact last-two-row channel square

Assume that the two high strands stay horizontally increasing on every row
before the terminal freeze.  R171 shows that their first order flip is then
the terminal row and is an exact vertical eviction of the target `v`.

The target has a strict-left relay on row `v-1`.  Combining that relay with
the horizontal parked handoff gives an exact checkerboard of the two source
channels `R` (old rows) and `C` (current prefix):

```
                 (v-1,c)   (v-1,r)     (v,c)      (v,r)
target in R          yes        no         yes         no
target in C          yes        yes        no          no
```

Here `c=r-1`.  Meanwhile `q=v-3` is absent from both exact column histories,
but owner coverage supplies it stably through a non-tail channel in all four
sources.  Thus neither target-channel bookkeeping nor the preview-history
bit alone contradicts the last transition.  What remains is a genuinely
global relay-to-right-history exchange statement.
-/

/-- Exact `R/C` channel square of the target on the last two braid rows. -/
structure TerminalTargetHistoryPrefixCheckerboard
    (f : Nat -> Nat -> Nat) (v r : Nat) : Prop where
  oldLeftHistory : R f (v - 1) (r - 1) v
  oldLeftPrefix : C f (v - 1) (r - 1) v
  oldRightNoHistory : Not (R f (v - 1) r v)
  oldRightPrefix : C f (v - 1) r v
  newLeftHistory : R f v (r - 1) v
  newLeftNoPrefix : Not (C f v (r - 1) v)
  newRightNoHistory : Not (R f v r v)
  newRightNoPrefix : Not (C f v r v)

/-- Complete theorem-grade normal form for an all-interior-ascent failed
braid.  Besides the target checkerboard, it records the unique strict-left
relay on row `v-1`, both MEX rows, and the fact that `q=v-3` is history-free
yet stably present in all four sources through its lower owner. -/
structure TerminalOnlyHighBraidLastTwoRowsPacket
    (v r g a : Nat) : Prop where
  braid : FailedTerminalDeepHistoryHighBraidPacket v r g a
  allInteriorAscent : forall t, a <= t -> t < v ->
    gameF t (r - 1) < gameF t r
  targetRelay : exists b,
    b < r - 1 /\
    gameF (v - 1) b = v /\
    forall b', b' <= v - 1 -> gameF (v - 1) b' = v -> b' = b
  previousRow :
    IsMex (B gameF (v - 1) (r - 1)) (gameF (v - 1) (r - 1)) /\
    IsMex (B gameF (v - 1) r) (gameF (v - 1) r) /\
    v < gameF (v - 1) (r - 1) /\
    gameF (v - 1) (r - 1) < gameF (v - 1) r
  terminalRow :
    IsMex (B gameF v (r - 1)) (gameF v (r - 1)) /\
    IsMex (B gameF v r) v /\
    v < gameF v (r - 1) /\
    gameF v r = v
  targetChannels : TerminalTargetHistoryPrefixCheckerboard gameF v r
  previewHistoriesAbsent :
    Not (ColHistPred gameF v (r - 1) (v - 3)) /\
    Not (ColHistPred gameF v r (v - 3))
  previewFinalTailsAbsent :
    Not (ColTail gameF (v - 1) (r - 1) (v - 3)) /\
    Not (ColTail gameF (v - 1) r (v - 3)) /\
    Not (ColTail gameF v (r - 1) (v - 3)) /\
    Not (ColTail gameF v r (v - 3))
  previewOwnerFinalChannel :
    (exists d, d <= g /\ d < r - 1 /\ gameF d d = v - 3) \/
    (exists s, s <= g /\ s < r - 1 /\ s < v - 3 /\
      gameF (v - 3) s = v - 3 /\
      gameF (v - 1) s = v - 3 /\ gameF v s = v - 3)
  previewFinalSources :
    B gameF (v - 1) (r - 1) (v - 3) /\
    B gameF (v - 1) r (v - 3) /\
    B gameF v (r - 1) (v - 3) /\
    B gameF v r (v - 3)

/-- The all-interior-ascent case forces the complete last-two-row packet. -/
theorem gameF_failedTerminalHighBraid_allInteriorAscent_lastTwoRows
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (hascent : forall t, a <= t -> t < v ->
      gameF t (r - 1) < gameF t r) :
    TerminalOnlyHighBraidLastTwoRowsPacket v r g a := by
  rcases gameF_failed_terminal_history_highBraid_has_firstFlip hbraid with
      ⟨t, hflip⟩
  have htv : t = v := by
    have hnotlt : Not (t < v) := by
      intro hlt
      have hasc := hascent t (Nat.le_of_lt hflip.flipRange.1) hlt
      have hdesc := hflip.currentDescent
      omega
    have hle := hflip.flipRange.2
    omega
  subst t
  rcases firstTerminalHighBraidFlip_terminal_exact_target_eviction hflip with
      ⟨hstart, hprevRightHigh, _hdrop, hOldRightPrefix,
        hOldRightNoHistory, _hOldRightNe, hNewRightNoPrefix⟩
  have hadeep := hbraid.oldHostChronology.2
  have hra := hbraid.oldHostChronology.1
  have hrv := hbraid.terminal.1
  have hprev := hbraid.interiorHighBraid
    (v - 1) (by omega) (by omega)
  have hprevAscent := hascent (v - 1) (by omega) (by omega)

  rcases gameF_deep_terminal_target_rehosts_strictly_left
      hrv hstart hra (by omega : a < v - 1) (by omega : v - 1 < v)
      hbraid.oldHost with ⟨b, hbc, hbhost⟩
  have hbrow : b <= v - 1 := by omega
  have hrelayUnique : forall b', b' <= v - 1 ->
      gameF (v - 1) b' = v -> b' = b := by
    intro b' hb'row hb'host
    exact gameRecurrenceModel.fixed_q_injective hb'row hbrow
      (hb'host.trans hbhost.symm)

  have hOldLeftHistory : R gameF (v - 1) (r - 1) v := by
    refine ⟨a, by omega, ?_⟩
    simpa [Nat.min_eq_right (by omega : r - 1 <= a)] using hbraid.oldHost
  have hOldLeftPrefix : C gameF (v - 1) (r - 1) v :=
    ⟨b, hbc, hbhost⟩
  have hNewLeftHistory : R gameF v (r - 1) v := by
    refine ⟨a, by omega, ?_⟩
    simpa [Nat.min_eq_right (by omega : r - 1 <= a)] using hbraid.oldHost
  have hNewLeftNoPrefix : Not (C gameF v (r - 1) v) :=
    by simpa [hstart] using hflip.horizontalHandoff.1.2.2
  have hNewRightHole : Not (B gameF v r v) := by
    simpa [hstart] using hflip.currentMex.2.2.1
  have hNewRightNoHistory : Not (R gameF v r v) := by
    intro hR
    exact hNewRightHole (Or.inl hR)
  have hchecker : TerminalTargetHistoryPrefixCheckerboard gameF v r := {
    oldLeftHistory := hOldLeftHistory
    oldLeftPrefix := hOldLeftPrefix
    oldRightNoHistory := hOldRightNoHistory
    oldRightPrefix := hOldRightPrefix
    newLeftHistory := hNewLeftHistory
    newLeftNoPrefix := hNewLeftNoPrefix
    newRightNoHistory := hNewRightNoHistory
    newRightNoPrefix := hNewRightNoPrefix
  }

  have hqOld := hbraid.previewAbsentHistories.1
  have hqNew := hbraid.previewAbsentHistories.2
  have noTail_of_noFullHistory : forall {top c}, top <= v ->
      Not (ColHistPred gameF v c (v - 3)) ->
      Not (ColTail gameF top c (v - 3)) := by
    intro top c htop hno
    rintro ⟨u, hutop, hcu, hu⟩
    exact hno ⟨u, Nat.le_of_lt hcu, by omega, hu⟩
  have hqTails :
      Not (ColTail gameF (v - 1) (r - 1) (v - 3)) /\
      Not (ColTail gameF (v - 1) r (v - 3)) /\
      Not (ColTail gameF v (r - 1) (v - 3)) /\
      Not (ColTail gameF v r (v - 3)) :=
    ⟨noTail_of_noFullHistory (by omega) hqOld,
      noTail_of_noFullHistory (by omega) hqNew,
      noTail_of_noFullHistory (Nat.le_refl v) hqOld,
      noTail_of_noFullHistory (Nat.le_refl v) hqNew⟩

  have hqpos : 0 < v - 3 := by omega
  have hqv : v - 3 < v := by omega
  rcases hbraid.owners (v - 3) hqpos hqv with
      ⟨d, hdg, hdiag⟩ | ⟨s, hsg, hsq, hrow⟩
  · have hdc : d < r - 1 := by
      have hfailure := hbraid.failure
      omega
    have diagSource : forall {top c}, d < top -> d <= c ->
        B gameF top c (v - 3) := by
      intro top c hdt hdc'
      left
      exact ⟨d, hdt, by simpa [Nat.min_eq_left hdc'] using hdiag⟩
    exact {
      braid := hbraid
      allInteriorAscent := hascent
      targetRelay := ⟨b, hbc, hbhost, hrelayUnique⟩
      previousRow := ⟨hprev.1, hprev.2.2.1, hprev.2.1, hprevAscent⟩
      terminalRow := ⟨hbraid.terminalPredecessorMex,
        by simpa [hstart] using hflip.currentMex.2,
        hbraid.terminalPredecessorHigh, hstart⟩
      targetChannels := hchecker
      previewHistoriesAbsent := ⟨hqOld, hqNew⟩
      previewFinalTailsAbsent := hqTails
      previewOwnerFinalChannel := Or.inl ⟨d, hdg, hdc, hdiag⟩
      previewFinalSources :=
        ⟨diagSource (by omega) (by omega),
          diagSource (by omega) (by omega),
          diagSource (by omega) (by omega),
          diagSource (by omega) (by omega)⟩
    }
  · have hsc : s < r - 1 := by
      have hfailure := hbraid.failure
      omega
    have hqPrev : gameF (v - 1) s = v - 3 :=
      gameF_freeze_persists hsq hrow (by omega)
    have hqNow : gameF v s = v - 3 :=
      gameF_freeze_persists hsq hrow (by omega)
    exact {
      braid := hbraid
      allInteriorAscent := hascent
      targetRelay := ⟨b, hbc, hbhost, hrelayUnique⟩
      previousRow := ⟨hprev.1, hprev.2.2.1, hprev.2.1, hprevAscent⟩
      terminalRow := ⟨hbraid.terminalPredecessorMex,
        by simpa [hstart] using hflip.currentMex.2,
        hbraid.terminalPredecessorHigh, hstart⟩
      targetChannels := hchecker
      previewHistoriesAbsent := ⟨hqOld, hqNew⟩
      previewFinalTailsAbsent := hqTails
      previewOwnerFinalChannel := Or.inr
        ⟨s, hsg, hsc, hsq, hrow, hqPrev, hqNow⟩
      previewFinalSources :=
        ⟨Or.inr ⟨s, hsc, hqPrev⟩,
          Or.inr ⟨s, by omega, hqPrev⟩,
          Or.inr ⟨s, hsc, hqNow⟩,
          Or.inr ⟨s, by omega, hqNow⟩⟩
    }

/-- The exact remaining global bridge: an all-ascent relay packet would have
to return the target to the old right history.  R172 proves every local
premise and proves that the actual terminal eviction has the opposite bit. -/
def TerminalOnlyHighBraidRelayForcesRightHistory : Prop :=
  forall {v r g a : Nat},
    TerminalOnlyHighBraidLastTwoRowsPacket v r g a ->
    R gameF (v - 1) r v

theorem gameF_no_allInteriorAscent_failedBraid_of_relayForcesRightHistory
    (hexchange : TerminalOnlyHighBraidRelayForcesRightHistory)
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (hascent : forall t, a <= t -> t < v ->
      gameF t (r - 1) < gameF t r) : False := by
  have hpacket :=
    gameF_failedTerminalHighBraid_allInteriorAscent_lastTwoRows hbraid hascent
  exact hpacket.targetChannels.oldRightNoHistory (hexchange hpacket)

/-! ## Local realizability audit of the last-two-row square -/

/-- A finite local source frame realizing the final two rows with
`v=20`, `q=17`, `c=5`, and `r=6`.  It is deliberately only a source frame,
not a second global Chomp recurrence. -/
def r172TerminalCornerFrame (q b : Nat) : Nat :=
  if q = 15 ∧ b = 5 then 10
  else if q = 15 ∧ b = 6 then 10
  else if q = 17 ∧ b = 3 then 17
  else if q = 19 ∧ b = 0 then 7
  else if q = 19 ∧ b = 1 then 8
  else if q = 19 ∧ b = 2 then 9
  else if q = 19 ∧ b = 3 then 17
  else if q = 19 ∧ b = 4 then 20
  else if q = 19 ∧ b = 5 then 21
  else if q = 19 ∧ b = 6 then 22
  else if q = 20 ∧ b = 0 then 7
  else if q = 20 ∧ b = 1 then 8
  else if q = 20 ∧ b = 2 then 9
  else if q = 20 ∧ b = 3 then 17
  else if q = 20 ∧ b = 4 then 10
  else if q = 20 ∧ b = 5 then 22
  else if q = 20 ∧ b = 6 then 20
  else r168PreviewAbsentFrame q b

theorem r172_corner_B_19_5_exact :
    BValueList r172TerminalCornerFrame 19 5 =
      [1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 20, 15, 16, 18, 19,
       10, 17105, 18105, 19105, 7, 8, 9, 17, 20] := by
  decide

theorem r172_corner_B_19_6_exact :
    BValueList r172TerminalCornerFrame 19 6 =
      [1, 2, 3, 4, 5, 6, 7106, 11, 12, 13, 14, 15, 16, 18, 19,
       10, 17106, 18106, 19106, 7, 8, 9, 17, 20, 21] := by
  decide

theorem r172_corner_B_20_5_exact :
    BValueList r172TerminalCornerFrame 20 5 =
      [1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 20, 15, 16, 18, 19,
       10, 17105, 18105, 19105, 21, 7, 8, 9, 17, 10] := by
  decide

theorem r172_corner_B_20_6_exact :
    BValueList r172TerminalCornerFrame 20 6 =
      [1, 2, 3, 4, 5, 6, 7106, 11, 12, 13, 14, 15, 16, 18, 19,
       10, 17106, 18106, 19106, 22, 7, 8, 9, 17, 10, 22] := by
  decide

theorem r172_corner_R_19_5_exact :
    RValueList r172TerminalCornerFrame 19 5 =
      [1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 20, 15, 16, 18, 19,
       10, 17105, 18105, 19105] := by
  decide

theorem r172_corner_C_19_5_exact :
    CValueList r172TerminalCornerFrame 19 5 = [7, 8, 9, 17, 20] := by
  decide

theorem r172_corner_R_19_6_exact :
    RValueList r172TerminalCornerFrame 19 6 =
      [1, 2, 3, 4, 5, 6, 7106, 11, 12, 13, 14, 15, 16, 18, 19,
       10, 17106, 18106, 19106] := by
  decide

theorem r172_corner_C_19_6_exact :
    CValueList r172TerminalCornerFrame 19 6 = [7, 8, 9, 17, 20, 21] := by
  decide

theorem r172_corner_R_20_5_exact :
    RValueList r172TerminalCornerFrame 20 5 =
      [1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 20, 15, 16, 18, 19,
       10, 17105, 18105, 19105, 21] := by
  decide

theorem r172_corner_C_20_5_exact :
    CValueList r172TerminalCornerFrame 20 5 = [7, 8, 9, 17, 10] := by
  decide

theorem r172_corner_R_20_6_exact :
    RValueList r172TerminalCornerFrame 20 6 =
      [1, 2, 3, 4, 5, 6, 7106, 11, 12, 13, 14, 15, 16, 18, 19,
       10, 17106, 18106, 19106, 22] := by
  decide

theorem r172_corner_C_20_6_exact :
    CValueList r172TerminalCornerFrame 20 6 =
      [7, 8, 9, 17, 10, 22] := by
  decide

theorem r172_corner_oldLeft_isMex :
    IsMex (B r172TerminalCornerFrame 19 5) 21 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 21 ∈ BValueList r172TerminalCornerFrame 19 5 :=
      mem_BValueList_iff.mpr hB
    rw [r172_corner_B_19_5_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r172_corner_B_19_5_exact]
    simp
    omega

theorem r172_corner_oldRight_isMex :
    IsMex (B r172TerminalCornerFrame 19 6) 22 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 22 ∈ BValueList r172TerminalCornerFrame 19 6 :=
      mem_BValueList_iff.mpr hB
    rw [r172_corner_B_19_6_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r172_corner_B_19_6_exact]
    simp
    omega

theorem r172_corner_newLeft_isMex :
    IsMex (B r172TerminalCornerFrame 20 5) 22 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 22 ∈ BValueList r172TerminalCornerFrame 20 5 :=
      mem_BValueList_iff.mpr hB
    rw [r172_corner_B_20_5_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r172_corner_B_20_5_exact]
    simp
    omega

theorem r172_corner_newRight_isMex :
    IsMex (B r172TerminalCornerFrame 20 6) 20 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem : 20 ∈ BValueList r172TerminalCornerFrame 20 6 :=
      mem_BValueList_iff.mpr hB
    rw [r172_corner_B_20_6_exact] at hmem
    simp at hmem
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    rw [r172_corner_B_20_6_exact]
    simp
    omega

theorem r172_corner_target_checkerboard :
    TerminalTargetHistoryPrefixCheckerboard
      r172TerminalCornerFrame 20 6 := by
  constructor
  · apply mem_RValueList_iff.mp
    rw [r172_corner_R_19_5_exact]
    simp
  · apply mem_CValueList_iff.mp
    rw [r172_corner_C_19_5_exact]
    simp
  · intro hR
    have hmem := mem_RValueList_iff.mpr hR
    rw [r172_corner_R_19_6_exact] at hmem
    simp at hmem
  · apply mem_CValueList_iff.mp
    rw [r172_corner_C_19_6_exact]
    simp
  · apply mem_RValueList_iff.mp
    rw [r172_corner_R_20_5_exact]
    simp
  · intro hC
    have hmem := mem_CValueList_iff.mpr hC
    rw [r172_corner_C_20_5_exact] at hmem
    simp at hmem
  · intro hR
    have hmem := mem_RValueList_iff.mpr hR
    rw [r172_corner_R_20_6_exact] at hmem
    simp at hmem
  · intro hC
    have hmem := mem_CValueList_iff.mpr hC
    rw [r172_corner_C_20_6_exact] at hmem
    simp at hmem

theorem r172_corner_preview_absent_old_history :
    Not (ColHistPred r172TerminalCornerFrame 20 5 17) := by
  rintro ⟨u, h5u, hu20, hvalue⟩
  have hR : R r172TerminalCornerFrame 20 5 17 := by
    exact ⟨u, hu20, by simpa [Nat.min_eq_right h5u] using hvalue⟩
  have hmem := mem_RValueList_iff.mpr hR
  rw [r172_corner_R_20_5_exact] at hmem
  simp at hmem

theorem r172_corner_preview_absent_new_history :
    Not (ColHistPred r172TerminalCornerFrame 20 6 17) := by
  rintro ⟨u, h6u, hu20, hvalue⟩
  have hR : R r172TerminalCornerFrame 20 6 17 := by
    exact ⟨u, hu20, by simpa [Nat.min_eq_right h6u] using hvalue⟩
  have hmem := mem_RValueList_iff.mpr hR
  rw [r172_corner_R_20_6_exact] at hmem
  simp at hmem

structure R172TerminalCornerLocalInterface : Prop where
  oldLeftMex : IsMex (B r172TerminalCornerFrame 19 5) 21
  oldRightMex : IsMex (B r172TerminalCornerFrame 19 6) 22
  newLeftMex : IsMex (B r172TerminalCornerFrame 20 5) 22
  newRightMex : IsMex (B r172TerminalCornerFrame 20 6) 20
  rowValues :
    r172TerminalCornerFrame 19 5 = 21 /\
    r172TerminalCornerFrame 19 6 = 22 /\
    r172TerminalCornerFrame 20 5 = 22 /\
    r172TerminalCornerFrame 20 6 = 20
  targetRelay : r172TerminalCornerFrame 19 4 = 20
  targetChannels : TerminalTargetHistoryPrefixCheckerboard
    r172TerminalCornerFrame 20 6
  previewOwnerPersistence :
    r172TerminalCornerFrame 17 3 = 17 /\
    r172TerminalCornerFrame 19 3 = 17 /\
    r172TerminalCornerFrame 20 3 = 17
  previewHistoriesAbsent :
    Not (ColHistPred r172TerminalCornerFrame 20 5 17) /\
    Not (ColHistPred r172TerminalCornerFrame 20 6 17)
  previewFinalSources :
    B r172TerminalCornerFrame 19 5 17 /\
    B r172TerminalCornerFrame 19 6 17 /\
    B r172TerminalCornerFrame 20 5 17 /\
    B r172TerminalCornerFrame 20 6 17

/-- The complete two-row target checkerboard, all four exact MEX facts, the
strict-left target relay, and the history-free stable preview owner coexist
in a finite local source frame.  Consequently the missing exchange cannot be
derived from these last-two-row source facts alone. -/
theorem r172_terminalCorner_local_interface_counterframe :
    R172TerminalCornerLocalInterface := by
  refine {
    oldLeftMex := r172_corner_oldLeft_isMex
    oldRightMex := r172_corner_oldRight_isMex
    newLeftMex := r172_corner_newLeft_isMex
    newRightMex := r172_corner_newRight_isMex
    rowValues := by decide
    targetRelay := by decide
    targetChannels := r172_corner_target_checkerboard
    previewOwnerPersistence := by decide
    previewHistoriesAbsent :=
      ⟨r172_corner_preview_absent_old_history,
        r172_corner_preview_absent_new_history⟩
    previewFinalSources := ?_
  }
  exact ⟨by
      apply mem_BValueList_iff.mp
      rw [r172_corner_B_19_5_exact]
      simp,
    by
      apply mem_BValueList_iff.mp
      rw [r172_corner_B_19_6_exact]
      simp,
    by
      apply mem_BValueList_iff.mp
      rw [r172_corner_B_20_5_exact]
      simp,
    by
      apply mem_BValueList_iff.mp
      rw [r172_corner_B_20_6_exact]
      simp⟩

#print axioms gameF_failedTerminalHighBraid_allInteriorAscent_lastTwoRows
#print axioms gameF_no_allInteriorAscent_failedBraid_of_relayForcesRightHistory
#print axioms r172_corner_target_checkerboard
#print axioms r172_terminalCorner_local_interface_counterframe

end ChompLean
