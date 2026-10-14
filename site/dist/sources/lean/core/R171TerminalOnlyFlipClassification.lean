import R170TerminalHistoryHighBraidReduction

set_option autoImplicit false

namespace ChompLean

/-!
# The terminal-only high-braid flip is an exact target eviction

R170 leaves two vertical alternatives at the first horizontal order flip.
At a flip occurring on the terminal row itself, the strict-rise alternative
is impossible: the preceding right-strand value is already strictly above
the target, while the terminal right-strand value is exactly the target.

Thus a braid which stays left-to-right increasing on every interior row can
end only by the exact prefix-eviction branch.  This does not yet contradict
the recurrence, but it removes the `2 x 2` strict-rise alternative from the
terminal-only case and identifies the precise final transition that a
seeded chronology theorem must exclude.
-/

/-- Every pre-target cell strictly to the right of the lower-owner cutoff is
at least the target.  Owner coverage excludes carry and saturates the MEX
source at every positive lower value. -/
theorem gameF_ownerCovered_band_cell_ge_target
    {v g t e : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (htv : t < v)
    (hge : g < e)
    (het : e <= t) :
    v <= gameF t e := by
  have hnotCarry : Not (e < t /\ gameF (t - 1) e < t) :=
    gameF_noCarry_after_lowerOwnerCutoff htv hge howners
  have hmex : IsMex (B gameF t e) (gameF t e) :=
    gameF_brouwerRecurrence.2 het hnotCarry
  have hsat := gameF_ownerCovered_full_saturation
    (v := v) (g := g) (t := t) (e := e)
    howners htv hge het
  apply Nat.le_of_not_gt
  intro hlt
  exact hmex.2.1 (hsat (gameF t e) hmex.1 hlt)

/-- Consequently, every non-target entry of either braid strand before the
terminal row is strictly above `v`.  This explains why a realizable seeded
replacement of a history entry cannot evict a lower value inside the R170
packet: the only low-or-equal strand value is the distinguished old target
itself. -/
theorem failedTerminalHighBraid_nonTarget_strand_value_above
    {v r g a t e : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (he : e = r - 1 \/ e = r)
    (het : e <= t)
    (htv : t < v)
    (hne : Not (gameF t e = v)) :
    v < gameF t e := by
  have hge : g < e := by
    have hfailure := hbraid.failure
    rcases he with he | he
    · subst e
      omega
    · subst e
      omega
  have hle := gameF_ownerCovered_band_cell_ge_target
    hbraid.owners htv hge het
  omega

/-- If the certified first flip is the terminal row, then it is exactly a
vertical drop to `v`.  The target was in the previous row prefix at the
right strand, was not in its old-row channel, and is absent from the new row
prefix. -/
theorem firstTerminalHighBraidFlip_terminal_exact_target_eviction
    {v r g a : Nat}
    (hflip : FirstTerminalHighBraidFlipPacket v r g a v) :
    gameF v r = v /\
      v < gameF (v - 1) r /\
      gameF v r < gameF (v - 1) r /\
      C gameF (v - 1) r v /\
      Not (R gameF (v - 1) r v) /\
      Not (gameF (v - 1) r = v) /\
      Not (C gameF v r v) := by
  have hstart : gameF v r = v := hflip.braid.terminal.2
  have hadeep : a + 3 < v := hflip.braid.oldHostChronology.2
  have hprev := hflip.braid.interiorHighBraid
    (v - 1) (by omega : a < v - 1) (by omega : v - 1 < v)
  have hprevHigh : v < gameF (v - 1) r := hprev.2.2.2
  rcases hflip.verticalAlternative with hdrop | hrise
  · refine ⟨hstart, hprevHigh, ?_, ?_, ?_, ?_, ?_⟩
    · exact hdrop.1
    · simpa [hstart] using hdrop.2.1
    · simpa [hstart] using hdrop.2.2.1
    · simpa [hstart] using hdrop.2.2.2.1
    · simpa [hstart] using hdrop.2.2.2.2
  · rw [hstart] at hrise
    omega

/-- If every nonterminal row of a failed braid is a horizontal ascent, the
first flip supplied by R170 must be the terminal row, hence the terminal
transition is the exact target eviction above. -/
theorem failedTerminalHighBraid_allInteriorAscent_exact_target_eviction
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (hascent : forall t, a <= t -> t < v ->
      gameF t (r - 1) < gameF t r) :
    gameF v r = v /\
      v < gameF (v - 1) r /\
      gameF v r < gameF (v - 1) r /\
      C gameF (v - 1) r v /\
      Not (R gameF (v - 1) r v) /\
      Not (gameF (v - 1) r = v) /\
      Not (C gameF v r v) := by
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
  exact firstTerminalHighBraidFlip_terminal_exact_target_eviction hflip

#print axioms firstTerminalHighBraidFlip_terminal_exact_target_eviction
#print axioms failedTerminalHighBraid_allInteriorAscent_exact_target_eviction
#print axioms gameF_ownerCovered_band_cell_ge_target
#print axioms failedTerminalHighBraid_nonTarget_strand_value_above

end ChompLean
