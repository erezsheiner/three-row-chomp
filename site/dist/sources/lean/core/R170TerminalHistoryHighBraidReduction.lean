import R169TerminalHistoryExchangeClosure
import TailTransitionCore

set_option autoImplicit false

namespace ChompLean

/-!
# A first-failure terminal history is a two-column high braid

The unrestricted live-history exchange isolated in R168 is more global than
the upper-rail application actually needs.  At a strict failed rail we also
have lower-owner coverage.  Once an old target `v` is emitted at the
terminal predecessor `c = r - 1`, owner coverage and the propagated target
host force a much richer object:

* the old target is present in the exact history at `c` and absent at `r`;
* the preview value `v-3` is absent from both exact histories;
* the cell immediately to the right of the old emission is a MEX above `v`;
* on every later pre-freeze row, both adjacent cells `c` and `r` are MEXes
  strictly above `v`;
* the braid ends with a MEX above `v` at `(v,c)` and the freeze `v` at
  `(v,r)`.

Thus the scoped remaining obstruction is not an arbitrary old-history bit.
It is a deep one-row excursion of `v` into `c`, followed by a full adjacent
two-column high braid.  R164-style local frames do not validate the MEX
recurrence on the whole right-hand strand, so this package identifies the
global row-evolution information they omit.
-/

/-- A terminal freeze column cannot already be the freeze column of a
smaller blocker. -/
theorem gameF_terminal_freeze_column_live
    {v r : Nat}
    (_hrv : r < v)
    (hstart : gameF v r = v) :
    ColumnLiveBelow v r := by
  intro z hrz hzv hfreeze
  exact gameF_freeze_column_unique hrz hfreeze hzv hstart

/-- In a live column, occurrences of a lower value `z` after row `z` are
impossible.  Hence its history below `v` is exactly its pre-birth history
below `z`.  This is the useful fixed-column induction law supplied by exact
history evolution. -/
theorem gameF_colHistPred_cutoff_at_value_of_live
    {v c z : Nat}
    (hlive : ColumnLiveBelow v c)
    (hcz : c < z)
    (hzv : z < v) :
    ColHistPred gameF v c z <-> ColHistPred gameF z c z := by
  constructor
  · rintro ⟨t, hct, htv, hhost⟩
    by_cases htz : t < z
    · exact ⟨t, hct, htz, hhost⟩
    · have hzt : z <= t := Nat.le_of_not_gt htz
      have hlow : gameF t c <= t := by
        rw [hhost]
        exact hzt
      have hfreeze := gameF_low_cell_has_rowstart hct hlow
      have hzfreeze : gameF z c = z := by
        simpa [hhost] using hfreeze.2
      exact False.elim ((hlive z hcz hzv) hzfreeze)
  · exact colHistPred_mono_top (Nat.le_of_lt hzv)

/-- Owner coverage plus a target already in the source forces a post-cutoff
pre-freeze cell strictly above that target. -/
theorem gameF_ownerCovered_cell_above_target_of_source
    {v g t e : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (htv : t < v)
    (hge : g < e)
    (het : e <= t)
    (hBv : B gameF t e v) :
    v < gameF t e := by
  have hnotCarry : Not (e < t /\ gameF (t - 1) e < t) :=
    gameF_noCarry_after_lowerOwnerCutoff htv hge howners
  have hmex : IsMex (B gameF t e) (gameF t e) :=
    gameF_brouwerRecurrence.2 het hnotCarry
  have hsat := gameF_ownerCovered_full_saturation
    (v := v) (g := g) (t := t) (e := e)
    howners htv hge het
  apply Nat.lt_of_not_ge
  intro hle
  by_cases heq : gameF t e = v
  · apply hmex.2.1
    simpa [heq] using hBv
  · have hlt : gameF t e < v := by omega
    exact hmex.2.1 (hsat (gameF t e) hmex.1 hlt)

/-- Exact one-row law for adjacent MEX cells.  Either their outputs rise
from left to right, or the right output is a parked value which disappears
from the right source through every replacement channel.  In the latter
case the right MEX is a literal horizontal handoff of that parked value. -/
theorem adjacent_mex_order_or_exact_parked_handoff
    {f : Nat -> Nat -> Nat} {t e x y : Nat}
    (hmexLeft : IsMex (B f t e) x)
    (hmexRight : IsMex (B f t (e + 1)) y)
    (hne : Not (x = y)) :
    x < y \/
      (y < x /\
        ParkedOnly f t e y /\
        Not (e + 1 < t /\ f (e + 1) (e + 1) = y) /\
        Not (ColTail f t (e + 1) y) /\
        Not (f t e = y)) := by
  by_cases hxy : x < y
  · exact Or.inl hxy
  · have hyx : y < x := by omega
    have hleftY : B f t e y :=
      hmexLeft.2.2 y hmexRight.1 hyx
    have hrightHole : Not (B f t (e + 1) y) := hmexRight.2.1
    have hnormal :=
      (source_loss_iff_parked_and_no_replacement
        (f := f) (t := t) (e := e) (z := y)).mp
        ⟨hleftY, hrightHole⟩
    exact Or.inr ⟨hyx, hnormal⟩

/-- The exact scoped counterexample packet forced by a genuinely deep
terminal history witness at a strict first failure. -/
structure FailedTerminalDeepHistoryHighBraidPacket
    (v r g a : Nat) : Prop where
  targetLarge : 7 <= v
  terminal : r < v /\ gameF v r = v
  owners : LowerOwnerCoveredBy v g
  failure : g + 1 < r
  oldHostChronology : r <= a /\ a + 3 < v
  oldHost : gameF a (r - 1) = v
  targetHistoryEdit :
    ColHistPred gameF v (r - 1) v /\
      Not (ColHistPred gameF v r v)
  previewAbsentHistories :
    Not (ColHistPred gameF v (r - 1) (v - 3)) /\
      Not (ColHistPred gameF v r (v - 3))
  oldHostMex : IsMex (B gameF a (r - 1)) v
  rightOfOldHostMex : IsMex (B gameF a r) (gameF a r)
  rightOfOldHostHigh : v < gameF a r
  interiorHighBraid : forall t,
    a < t -> t < v ->
      IsMex (B gameF t (r - 1)) (gameF t (r - 1)) /\
      v < gameF t (r - 1) /\
      IsMex (B gameF t r) (gameF t r) /\
      v < gameF t r
  terminalPredecessorMex :
    IsMex (B gameF v (r - 1)) (gameF v (r - 1))
  terminalPredecessorHigh : v < gameF v (r - 1)

/-- A deep old target at a strict first failure forces the full history and
two-column high-braid packet. -/
theorem gameF_failed_deep_terminal_history_highBraid_packet
    {v r g a : Nat}
    (hv : 7 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= a)
    (hadeep : a + 3 < v)
    (hhost : gameF a (r - 1) = v) :
    FailedTerminalDeepHistoryHighBraidPacket v r g a := by
  have hav : a < v := by omega
  have hgc : g < r - 1 := by omega
  have hgr : g < r := by omega
  have hca : r - 1 <= a := by omega
  have hraA : r <= a := hra
  have hliveC : ColumnLiveBelow v (r - 1) :=
    lowerOwnerCoveredBy_columnLive_right_of_cutoff howners hgc
  have hliveR : ColumnLiveBelow v r :=
    gameF_terminal_freeze_column_live hrv hstart

  have hqOwner :
      (exists d, d < r - 1 /\ gameF d d = v - 3) \/
      (exists s, s < r - 1 /\ s < v - 3 /\
        gameF (v - 3) s = v - 3) := by
    rcases howners (v - 3) (by omega) (by omega) with
        ⟨d, hdg, hdiag⟩ | ⟨s, hsg, hsq, hrow⟩
    · exact Or.inl ⟨d, by omega, hdiag⟩
    · exact Or.inr ⟨s, by omega, hsq, hrow⟩
  have hhistory := gameF_deep_terminal_leftOwner_history_edit_normalForm
    hrv hstart hra hadeep hhost hqOwner

  have hOldMex : IsMex (B gameF a (r - 1)) v :=
    by simpa [hhost] using
      (gameF_cell_isMex_of_columnLiveBelow hliveC hca hav)

  have hrightBv : B gameF a r v := by
    right
    exact ⟨r - 1, by omega, hhost⟩
  have hRightMex : IsMex (B gameF a r) (gameF a r) :=
    gameF_cell_isMex_of_columnLiveBelow hliveR hraA hav
  have hRightHigh : v < gameF a r :=
    gameF_ownerCovered_cell_above_target_of_source
      howners hav hgr hraA hrightBv

  have hInterior : forall t,
      a < t -> t < v ->
        IsMex (B gameF t (r - 1)) (gameF t (r - 1)) /\
        v < gameF t (r - 1) /\
        IsMex (B gameF t r) (gameF t r) /\
        v < gameF t r := by
    intro t hat htv
    have hct : r - 1 <= t := by omega
    have hrt : r <= t := by omega
    have hleftBv : B gameF t (r - 1) v := by
      left
      exact ⟨a, hat, by simpa [Nat.min_eq_right hca] using hhost⟩
    rcases gameF_deep_terminal_target_rehosts_strictly_left
        hrv hstart hra hat htv hhost with ⟨b, hbc, hbhost⟩
    have hrightBv' : B gameF t r v := by
      right
      exact ⟨b, by omega, hbhost⟩
    exact ⟨
      gameF_cell_isMex_of_columnLiveBelow hliveC hct htv,
      gameF_ownerCovered_cell_above_target_of_source
        howners htv hgc hct hleftBv,
      gameF_cell_isMex_of_columnLiveBelow hliveR hrt htv,
      gameF_ownerCovered_cell_above_target_of_source
        howners htv hgr hrt hrightBv'⟩

  have hterminalEdge := gameF_failed_terminal_singleton_source_exchange
    (v := v) (r := r) (g := g) (by omega)
    hrv hstart howners hfailure

  exact {
    targetLarge := hv
    terminal := ⟨hrv, hstart⟩
    owners := howners
    failure := hfailure
    oldHostChronology := ⟨hra, hadeep⟩
    oldHost := hhost
    targetHistoryEdit := ⟨hhistory.1, hhistory.2.1⟩
    previewAbsentHistories := ⟨hhistory.2.2.1, hhistory.2.2.2⟩
    oldHostMex := hOldMex
    rightOfOldHostMex := hRightMex
    rightOfOldHostHigh := hRightHigh
    interiorHighBraid := hInterior
    terminalPredecessorMex := hterminalEdge.1
    terminalPredecessorHigh := hterminalEdge.2.1
  }

/-- Every interior row of the forced braid obeys the exact adjacent-MEX
handoff law.  This is the strongest genuinely one-step history evolution
available without a new global invariant: an arbitrarily long bad braid
must be a word of strict ascents and exact parked handoffs. -/
theorem gameF_failed_terminal_highBraid_row_word
    {v r g a t : Nat}
    (hpacket : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (hat : a < t)
    (htv : t < v) :
    let x := gameF t (r - 1)
    let y := gameF t r
    x < y \/
      (y < x /\
        ParkedOnly gameF t (r - 1) y /\
        Not (r < t /\ gameF r r = y) /\
        Not (ColTail gameF t r y) /\
        Not (gameF t (r - 1) = y)) := by
  dsimp only
  have hrow := hpacket.interiorHighBraid t hat htv
  have hrt : r <= t := by
    have hra := hpacket.oldHostChronology.1
    omega
  have hne : Not (gameF t (r - 1) = gameF t r) := by
    intro heq
    have hcols := gameRecurrenceModel.fixed_q_injective
      (q := t) (b₁ := r - 1) (b₂ := r)
      (by omega) hrt heq
    have hfail := hpacket.failure
    omega
  have hrpos : 0 < r := by
    have := hpacket.failure
    omega
  have hrsucc : (r - 1) + 1 = r := by omega
  have hmexRight :
      IsMex (B gameF t ((r - 1) + 1))
        (gameF t ((r - 1) + 1)) := by
    simpa only [hrsucc] using hrow.2.2.1
  have hne' :
      Not (gameF t (r - 1) = gameF t ((r - 1) + 1)) := by
    simpa only [hrsucc] using hne
  have hstep := adjacent_mex_order_or_exact_parked_handoff
    hrow.1 hmexRight hne'
  simpa only [hrsucc] using hstep

/-! ## The first horizontal order flip -/

/-- A bounded nonempty set of natural-number witnesses has a first witness
above its lower endpoint. -/
theorem exists_first_between
    (P : Nat -> Prop) {lo top : Nat}
    (hexists : exists t, lo < t /\ t <= top /\ P t) :
    exists t,
      lo < t /\ t <= top /\ P t /\
      forall s, lo < s -> s < t -> Not (P s) := by
  rcases hexists with ⟨t, ht⟩
  revert ht
  induction t using Nat.strongRecOn with
  | ind t ih =>
      intro ht
      by_cases hprevious : exists s, lo < s /\ s < t /\ P s
      · rcases hprevious with ⟨s, hlos, hst, hPs⟩
        exact ih s hst ⟨hlos, by omega, hPs⟩
      · refine ⟨t, ht.1, ht.2.1, ht.2.2, ?_⟩
        intro s hlos hst hPs
        exact hprevious ⟨s, hlos, hst, hPs⟩

/-- A genuine terminal freeze is itself on the MEX branch. -/
theorem gameF_terminal_freeze_isMex
    {v r : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v) :
    IsMex (B gameF v r) v := by
  have hnotCarry : Not (r < v /\ gameF (v - 1) r < v) := by
    rintro ⟨hrv', hlow⟩
    have hcopy := gameF_brouwerRecurrence.1 hrv' hlow
    rw [hstart] at hcopy
    omega
  have hmex := gameF_brouwerRecurrence.2
    (q := v) (r := r) (Nat.le_of_lt hrv) hnotCarry
  simpa [hstart] using hmex

/-- Complete certificate at the first row where the adjacent braid changes
from left-to-right ascent to right-to-left parked handoff. -/
structure FirstTerminalHighBraidFlipPacket
    (v r g a t : Nat) : Prop where
  braid : FailedTerminalDeepHistoryHighBraidPacket v r g a
  flipRange : a < t /\ t <= v
  previousAscent :
    gameF (t - 1) (r - 1) < gameF (t - 1) r
  currentDescent : gameF t r < gameF t (r - 1)
  previousMex :
    IsMex (B gameF (t - 1) (r - 1))
        (gameF (t - 1) (r - 1)) /\
      IsMex (B gameF (t - 1) r) (gameF (t - 1) r)
  currentMex :
    IsMex (B gameF t (r - 1)) (gameF t (r - 1)) /\
      IsMex (B gameF t r) (gameF t r)
  horizontalHandoff :
    ParkedOnly gameF t (r - 1) (gameF t r) /\
      Not (r < t /\ gameF r r = gameF t r) /\
      Not (ColTail gameF t r (gameF t r)) /\
      Not (gameF t (r - 1) = gameF t r)
  heightAlternative :
    (t = v /\ gameF t r = v) \/
      (t < v /\ v < gameF t r)
  verticalAlternative :
    (gameF t r < gameF (t - 1) r /\
      C gameF (t - 1) r (gameF t r) /\
      Not (R gameF (t - 1) r (gameF t r)) /\
      Not (gameF (t - 1) r = gameF t r) /\
      Not (C gameF t r (gameF t r))) \/
    (gameF (t - 1) (r - 1) < gameF (t - 1) r /\
      gameF (t - 1) r < gameF t r /\
      gameF t r < gameF t (r - 1))

/-- Every failed deep terminal braid has a first order flip.  At that row
the right output is an exact parked handoff.  Vertically, either the right
strand drops and the new hole is exactly an evicted previous-row prefix
value, or the surrounding `2 x 2` square is a strict four-term rise. -/
theorem gameF_failed_terminal_history_highBraid_has_firstFlip
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a) :
    exists t, FirstTerminalHighBraidFlipPacket v r g a t := by
  have hrv := hbraid.terminal.1
  have hstart := hbraid.terminal.2
  have hra := hbraid.oldHostChronology.1
  have hadeep := hbraid.oldHostChronology.2
  have hbaseAsc : gameF a (r - 1) < gameF a r := by
    rw [hbraid.oldHost]
    exact hbraid.rightOfOldHostHigh
  have htopDesc : gameF v r < gameF v (r - 1) := by
    rw [hstart]
    exact hbraid.terminalPredecessorHigh
  rcases exists_first_between
      (fun t => gameF t r < gameF t (r - 1))
      (lo := a) (top := v)
      ⟨v, by omega, Nat.le_refl v, htopDesc⟩ with
      ⟨t, hat, htvLe, hdesc, hfirst⟩
  have hrpos : 0 < r := by
    have := hbraid.failure
    omega
  have hrtPrev : r <= t - 1 := by omega
  have hprevNotDesc :
      Not (gameF (t - 1) r < gameF (t - 1) (r - 1)) := by
    by_cases hprevEqA : t - 1 = a
    · subst hprevEqA
      omega
    · apply hfirst (t - 1) (by omega) (by omega)
  have hprevNe :
      Not (gameF (t - 1) (r - 1) = gameF (t - 1) r) := by
    intro heq
    have hcols := gameRecurrenceModel.fixed_q_injective
      (q := t - 1) (b₁ := r - 1) (b₂ := r)
      (by omega) hrtPrev heq
    omega
  have hprevAsc :
      gameF (t - 1) (r - 1) < gameF (t - 1) r := by
    omega

  have hprevMex :
      IsMex (B gameF (t - 1) (r - 1))
          (gameF (t - 1) (r - 1)) /\
        IsMex (B gameF (t - 1) r) (gameF (t - 1) r) := by
    by_cases hprevEqA : t - 1 = a
    · subst hprevEqA
      exact ⟨by simpa [hbraid.oldHost] using hbraid.oldHostMex,
        hbraid.rightOfOldHostMex⟩
    · have hprevInterior := hbraid.interiorHighBraid
        (t - 1) (by omega) (by omega)
      exact ⟨hprevInterior.1, hprevInterior.2.2.1⟩

  have hcurrentMex :
      IsMex (B gameF t (r - 1)) (gameF t (r - 1)) /\
        IsMex (B gameF t r) (gameF t r) := by
    by_cases htv : t = v
    · subst t
      exact ⟨hbraid.terminalPredecessorMex,
        by simpa [hstart] using gameF_terminal_freeze_isMex hrv hstart⟩
    · have hcurrentInterior := hbraid.interiorHighBraid
        t hat (by omega)
      exact ⟨hcurrentInterior.1, hcurrentInterior.2.2.1⟩

  have hrsucc : (r - 1) + 1 = r := by omega
  have hmexRight' :
      IsMex (B gameF t ((r - 1) + 1))
        (gameF t ((r - 1) + 1)) := by
    simpa only [hrsucc] using hcurrentMex.2
  have hneCurrent :
      Not (gameF t (r - 1) = gameF t ((r - 1) + 1)) := by
    simpa only [hrsucc] using (show
      Not (gameF t (r - 1) = gameF t r) from (by omega))
  have hhorizontalRaw := adjacent_mex_order_or_exact_parked_handoff
    hcurrentMex.1 hmexRight' hneCurrent
  have hhorizontal :
      ParkedOnly gameF t (r - 1) (gameF t r) /\
        Not (r < t /\ gameF r r = gameF t r) /\
        Not (ColTail gameF t r (gameF t r)) /\
        Not (gameF t (r - 1) = gameF t r) := by
    rcases hhorizontalRaw with hasc | hhand
    · have hasc' : gameF t (r - 1) < gameF t r := by
        simpa only [hrsucc] using hasc
      omega
    · simpa only [hrsucc] using hhand.2

  have hheight :
      (t = v /\ gameF t r = v) \/
        (t < v /\ v < gameF t r) := by
    by_cases htv : t = v
    · subst t
      exact Or.inl ⟨rfl, hstart⟩
    · have hinterior := hbraid.interiorHighBraid t hat (by omega)
      exact Or.inr ⟨by omega, hinterior.2.2.2⟩

  have hrightNeVertical :
      Not (gameF (t - 1) r = gameF t r) := by
    intro heq
    have hprevEntry : B gameF t r (gameF (t - 1) r) := by
      left
      refine ⟨t - 1, by omega, ?_⟩
      simpa [Nat.min_eq_right hrtPrev]
    exact hcurrentMex.2.2.1 (by simpa [heq] using hprevEntry)

  have hvertical :
      (gameF t r < gameF (t - 1) r /\
        C gameF (t - 1) r (gameF t r) /\
        Not (R gameF (t - 1) r (gameF t r)) /\
        Not (gameF (t - 1) r = gameF t r) /\
        Not (C gameF t r (gameF t r))) \/
      (gameF (t - 1) (r - 1) < gameF (t - 1) r /\
        gameF (t - 1) r < gameF t r /\
        gameF t r < gameF t (r - 1)) := by
    by_cases hdrop : gameF t r < gameF (t - 1) r
    · have hprevCovered : B gameF (t - 1) r (gameF t r) :=
        hprevMex.2.2.2 (gameF t r) hcurrentMex.2.1 hdrop
      have hcurrentHole : Not (B gameF t r (gameF t r)) :=
        hcurrentMex.2.2.1
      have hbirth :=
        (vertical_hole_birth_iff_prefix_eviction
          (f := gameF) (r := t - 1) (c := r)
          (z := gameF t r) hrtPrev).mp ⟨hprevCovered, by
            have htidx : (t - 1) + 1 = t := by omega
            simpa only [htidx] using hcurrentHole⟩
      exact Or.inl ⟨hdrop, hbirth.1, hbirth.2.1,
        hrightNeVertical, by
          have htidx : (t - 1) + 1 = t := by omega
          simpa only [htidx] using hbirth.2.2.2⟩
    · have hrise : gameF (t - 1) r < gameF t r := by omega
      exact Or.inr ⟨hprevAsc, hrise, hdesc⟩

  exact ⟨t, {
    braid := hbraid
    flipRange := ⟨hat, htvLe⟩
    previousAscent := hprevAsc
    currentDescent := hdesc
    previousMex := hprevMex
    currentMex := hcurrentMex
    horizontalHandoff := hhorizontal
    heightAlternative := hheight
    verticalAlternative := hvertical
  }⟩

/-- In the prefix-eviction branch, the same handoff value has two exact old
certificates: a previous-row prefix host and an older tail occurrence in the
left column.  These certificates have only two possible chronological
orders.  If the tail occurrence is on the immediately previous row, row
injectivity identifies both certificates with the left cell.  Otherwise the
previous-row host is strictly farther left than the left braid column. -/
theorem gameF_firstFlip_prefixEviction_host_normalForm
    {v r g a t : Nat}
    (hflip : FirstTerminalHighBraidFlipPacket v r g a t)
    (hdrop : gameF t r < gameF (t - 1) r) :
    exists b h,
      b < r /\
      gameF (t - 1) b = gameF t r /\
      h < t /\
      r - 1 < h /\
      gameF h (r - 1) = gameF t r /\
      ((h = t - 1 /\ b = r - 1 /\
          gameF (t - 1) (r - 1) = gameF t r) \/
        (h < t - 1 /\ b < r - 1)) := by
  have hvertical :
      C gameF (t - 1) r (gameF t r) := by
    rcases hflip.verticalAlternative with hevict | hrise
    · exact hevict.2.1
    · omega
  rcases hvertical with ⟨b, hbr, hbhost⟩
  rcases hflip.horizontalHandoff.1.1 with ⟨h, hht, hrh, hhhost⟩
  refine ⟨b, h, hbr, hbhost, hht, hrh, hhhost, ?_⟩
  by_cases hlast : h = t - 1
  · left
    have hbt : b <= t - 1 := by
      have hra := hflip.braid.oldHostChronology.1
      have hat := hflip.flipRange.1
      omega
    have hct : r - 1 <= t - 1 := by
      have hra := hflip.braid.oldHostChronology.1
      have hat := hflip.flipRange.1
      omega
    have hbEq : b = r - 1 := by
      apply gameRecurrenceModel.fixed_q_injective hbt hct
      change gameF (t - 1) b = gameF (t - 1) (r - 1)
      have hleftValue :
          gameF (t - 1) (r - 1) = gameF t r := by
        simpa only [hlast] using hhhost
      exact hbhost.trans hleftValue.symm
    exact ⟨hlast, hbEq, by simpa only [hlast] using hhhost⟩
  · right
    have hhlt : h < t - 1 := by omega
    refine ⟨hhlt, ?_⟩
    have hble : b <= r - 1 := by omega
    apply Nat.lt_of_le_of_ne hble
    intro hbEq
    have hsource : B gameF (t - 1) (r - 1) (gameF t r) := by
      left
      refine ⟨h, hhlt, ?_⟩
      simpa [Nat.min_eq_right (Nat.le_of_lt hrh)] using hhhost
    have hpreviousValue :
        gameF (t - 1) (r - 1) = gameF t r := by
      simpa only [hbEq] using hbhost
    exact hflip.previousMex.1.2.1
      (by simpa only [hpreviousValue] using hsource)

/-- If the first flip is not a vertical drop, the strict-rise square spends a
quantifiable amount of the left-cell source capacity.  A flip immediately
after the old target host needs four terminal columns; every later flip needs
five.  This is the exact local capacity consequence; by itself it does not
contradict the failed-band geometry. -/
theorem gameF_firstFlip_strictRise_capacity
    {v r g a t : Nat}
    (hflip : FirstTerminalHighBraidFlipPacket v r g a t)
    (hnoDrop : Not (gameF t r < gameF (t - 1) r)) :
    t < v /\
      gameF t (r - 1) - 1 <= t + (r - 1) /\
      ((t = a + 1 /\
          gameF (t - 1) (r - 1) = v /\
          v + 3 <= gameF t (r - 1) /\ 4 <= r) \/
        (a + 1 < t /\
          v < gameF (t - 1) (r - 1) /\
          v + 4 <= gameF t (r - 1) /\ 5 <= r)) := by
  have hchain :
      gameF (t - 1) (r - 1) < gameF (t - 1) r /\
      gameF (t - 1) r < gameF t r /\
      gameF t r < gameF t (r - 1) := by
    rcases hflip.verticalAlternative with hevict | hrise
    · exact False.elim (hnoDrop hevict.1)
    · exact hrise
  have hprevRightHigh : v < gameF (t - 1) r := by
    by_cases hbase : t - 1 = a
    · simpa only [hbase] using hflip.braid.rightOfOldHostHigh
    · have hat := hflip.flipRange.1
      have htvLe := hflip.flipRange.2
      exact (hflip.braid.interiorHighBraid (t - 1)
        (by omega) (by omega)).2.2.2
  have htv : t < v := by
    rcases hflip.heightAlternative with hterminal | hinterior
    · omega
    · exact hinterior.1
  have hrt : r - 1 <= t := by
    have hra := hflip.braid.oldHostChronology.1
    have hat := hflip.flipRange.1
    omega
  have hcurrentHigh : t < gameF t (r - 1) := by
    rcases hflip.heightAlternative with hterminal | hinterior <;> omega
  have hcapacity : gameF t (r - 1) - 1 <= t + (r - 1) :=
    high_cell_output_source_capacity gameRecurrenceModel
      hrt hcurrentHigh (Eq.refl (gameF t (r - 1)))
  have hrpos : 0 < r := by
    have hfailure := hflip.braid.failure
    omega
  have hcapacityLinear : gameF t (r - 1) <= t + r := by
    have hxpred : gameF t (r - 1) - 1 + 1 = gameF t (r - 1) :=
      Nat.sub_add_cancel (by omega)
    have hrpred : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
    omega
  refine ⟨htv, hcapacity, ?_⟩
  by_cases hbase : t - 1 = a
  · left
    have hleftEq : gameF (t - 1) (r - 1) = v := by
      simpa only [hbase] using hflip.braid.oldHost
    have hcurrentLower : v + 3 <= gameF t (r - 1) := by omega
    exact ⟨by omega, hleftEq, hcurrentLower, by omega⟩
  · right
    have hat := hflip.flipRange.1
    have htvLe := hflip.flipRange.2
    have hleftHigh : v < gameF (t - 1) (r - 1) :=
      (hflip.braid.interiorHighBraid (t - 1)
        (by omega) (by omega)).2.1
    have hcurrentLower : v + 4 <= gameF t (r - 1) := by omega
    exact ⟨by omega, hleftHigh, hcurrentLower, by omega⟩

/-- Scoped global atom left by the reduction.  It only forbids the rich
first-failure braid packet above; it says nothing about arbitrary live
terminal columns. -/
def NoFailedTerminalDeepHistoryHighBraid : Prop :=
  forall {v r g a : Nat},
    FailedTerminalDeepHistoryHighBraidPacket v r g a -> False

/-- The scoped no-braid law already closes the upper rail directly. -/
theorem gameF_upperRail_of_noFailedTerminalDeepHistoryHighBraid
    {q r g H : Nat}
    (hq : 4 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hnoBraid : NoFailedTerminalDeepHistoryHighBraid) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  rcases gameF_firstFailure_forces_early_terminal_sighting
      (by omega) hrv hstart howners hfailure hinterior
      hpreviewLe hpreviewLeft hpreview with ⟨a, hra, haq, hhost⟩
  have hpacket := gameF_failed_deep_terminal_history_highBraid_packet
    (v := q + 3) (r := r) (g := g) (a := a)
    (by omega) hrv hstart howners hfailure hra (by omega) hhost
  exact hnoBraid hpacket

#print axioms gameF_terminal_freeze_column_live
#print axioms gameF_colHistPred_cutoff_at_value_of_live
#print axioms gameF_ownerCovered_cell_above_target_of_source
#print axioms adjacent_mex_order_or_exact_parked_handoff
#print axioms gameF_failed_deep_terminal_history_highBraid_packet
#print axioms gameF_failed_terminal_highBraid_row_word
#print axioms exists_first_between
#print axioms gameF_terminal_freeze_isMex
#print axioms gameF_failed_terminal_history_highBraid_has_firstFlip
#print axioms gameF_firstFlip_prefixEviction_host_normalForm
#print axioms gameF_firstFlip_strictRise_capacity
#print axioms gameF_upperRail_of_noFailedTerminalDeepHistoryHighBraid

end ChompLean
