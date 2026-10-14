import R172TerminalOnlyBraidLastTwoRowsNormalForm

set_option autoImplicit false

namespace ChompLean

/-!
# R173: terminal-only braid relay trajectory audit

R172 isolated a proposed final exchange principle saying that the target of
a terminal freeze must reappear in the old-row channel `R` at the terminal
column.  The first result below shows that this conclusion is not merely
hard: it is forbidden by the row-start geometry for every terminal freeze.
Consequently that proposed principle is exactly a disguised assertion that
the all-ascent failed-braid packet does not exist.

The rest of the file records the honest global information that is available
without such an assertion.  The target has a prefix relay on every active
row, relay columns cannot repeat, and the old-row channel at the freeze
column is empty throughout.  On a high braid this gives an exact all-row
target-channel schedule.  Finally, any parked value below an ascending left
strand must acquire either the new diagonal owner or a new-column tail on
the right.  An unreplaced parked witness is therefore a sufficient, genuinely
structural remaining atom.
-/

/-! ## The proposed right-history conclusion is universally impossible -/

/-- A row-start target never belongs to the old-row channel at its freeze
column on any earlier row.  This is the direct specialized form of
`RecurrenceModel.rowstart_not_R`. -/
theorem r173_terminalFreeze_rightHistory_empty
    {v r t : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (htv : t < v) :
    Not (R gameF t r v) :=
  gameRecurrenceModel.rowstart_not_R hstart hrv htv

/-- In particular, the conclusion requested by the R172 relay atom is false
on every packet to which that atom could be applied. -/
theorem r173_terminalOnlyPacket_rightHistory_impossible
    {v r g a : Nat}
    (hpacket : TerminalOnlyHighBraidLastTwoRowsPacket v r g a) :
    Not (R gameF (v - 1) r v) := by
  have hrv := hpacket.braid.terminal.1
  exact r173_terminalFreeze_rightHistory_empty
    hrv hpacket.braid.terminal.2 (by omega)

/-- The direct no-counterexample statement hidden behind the R172 exchange
atom. -/
def R173NoAllInteriorAscentFailedTerminalHighBraid : Prop :=
  forall {v r g a : Nat},
    FailedTerminalDeepHistoryHighBraidPacket v r g a ->
    (forall t, a <= t -> t < v ->
      gameF t (r - 1) < gameF t r) ->
    False

/-- The R172 relay atom is logically equivalent to simply postulating that
there is no all-interior-ascent failed braid.  Its advertised right-history
conclusion contributes no independent recurrence content. -/
theorem r173_relayForcesRightHistory_iff_noAllInteriorAscentFailedBraid :
    TerminalOnlyHighBraidRelayForcesRightHistory <->
      R173NoAllInteriorAscentFailedTerminalHighBraid := by
  constructor
  · intro hexchange v r g a hbraid hascent
    exact gameF_no_allInteriorAscent_failedBraid_of_relayForcesRightHistory
      hexchange hbraid hascent
  · intro hno v r g a hpacket
    exact False.elim (hno hpacket.braid hpacket.allInteriorAscent)

/-! ## Honest terminal-relay trajectory -/

/-- Global trajectory facts forced by a terminal row start.  Every active
row has a current-prefix host, no fixed prefix column can host the target on
two active rows, and the old-row channel at the terminal column is empty. -/
structure R173TerminalFreezeRelayTrajectory (v r : Nat) : Prop where
  terminal : r < v /\ gameF v r = v
  activeHost : forall t, r < t -> t < v ->
    exists b, b < r /\ gameF t b = v
  activeHostColumnNoRepeat : forall {t1 t2 b},
    r < t1 -> t1 < t2 -> t2 < v -> b < r ->
    gameF t1 b = v -> gameF t2 b = v -> False
  rightHistoryEmpty : forall t, t < v -> Not (R gameF t r v)

/-- Every actual terminal freeze carries the complete relay trajectory above. -/
theorem r173_terminalFreeze_relayTrajectory
    {v r : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v) :
    R173TerminalFreezeRelayTrajectory v r := by
  refine {
    terminal := ⟨hrv, hstart⟩
    activeHost := ?_
    activeHostColumnNoRepeat := ?_
    rightHistoryEmpty := ?_
  }
  · intro t hrt htv
    exact rowStartPropagation gameRecurrenceModel hstart hrv hrt htv
  · intro t1 t2 b hrt1 ht12 ht2v hbr hhost1 hhost2
    exact encoding_same_lower_no_repeat game_encodes
      (Nat.lt_trans hbr hrt1) ht12 ht2v hhost1 hhost2
  · intro t htv
    exact r173_terminalFreeze_rightHistory_empty hrv hstart htv

/-! ## Exact target channels on every interior braid row -/

/-- The target-channel normal form on one arbitrary interior braid row.
The strict-left relay is unique on the row, the old host supplies left
history, and the terminal row start forbids right history. -/
structure R173TerminalTargetInteriorChannels
    (v r a t : Nat) : Prop where
  rowRange : a < t /\ t < v
  targetRelay : exists b,
    b < r - 1 /\
    gameF t b = v /\
    forall b', b' <= t -> gameF t b' = v -> b' = b
  leftHistory : R gameF t (r - 1) v
  leftPrefix : C gameF t (r - 1) v
  rightHistoryEmpty : Not (R gameF t r v)
  rightPrefix : C gameF t r v
  leftMex : IsMex (B gameF t (r - 1)) (gameF t (r - 1))
  rightMex : IsMex (B gameF t r) (gameF t r)
  strandsAboveTarget :
    v < gameF t (r - 1) /\ v < gameF t r

/-- The R172 last-two-row checkerboard is the endpoint of an all-row
schedule: on every interior row the target lies in both left channels, only
the current-prefix channel on the right, and never the right history. -/
theorem r173_failedTerminalHighBraid_interior_targetChannels
    {v r g a t : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (hat : a < t)
    (htv : t < v) :
    R173TerminalTargetInteriorChannels v r a t := by
  have hrv := hbraid.terminal.1
  have hstart := hbraid.terminal.2
  have hra := hbraid.oldHostChronology.1
  have hrow := hbraid.interiorHighBraid t hat htv
  rcases gameF_deep_terminal_target_rehosts_strictly_left
      hrv hstart hra hat htv hbraid.oldHost with ⟨b, hbc, hbhost⟩
  have hbrow : b <= t := by omega
  have hrelayUnique : forall b', b' <= t ->
      gameF t b' = v -> b' = b := by
    intro b' hb'row hb'host
    exact gameRecurrenceModel.fixed_q_injective hb'row hbrow
      (hb'host.trans hbhost.symm)
  have hleftHistory : R gameF t (r - 1) v := by
    refine ⟨a, hat, ?_⟩
    simpa [Nat.min_eq_right (by omega : r - 1 <= a)] using hbraid.oldHost
  have hleftPrefix : C gameF t (r - 1) v :=
    ⟨b, hbc, hbhost⟩
  have hrightPrefix : C gameF t r v :=
    ⟨b, by omega, hbhost⟩
  exact {
    rowRange := ⟨hat, htv⟩
    targetRelay := ⟨b, hbc, hbhost, hrelayUnique⟩
    leftHistory := hleftHistory
    leftPrefix := hleftPrefix
    rightHistoryEmpty :=
      r173_terminalFreeze_rightHistory_empty hrv hstart htv
    rightPrefix := hrightPrefix
    leftMex := hrow.1
    rightMex := hrow.2.2.1
    strandsAboveTarget := ⟨hrow.2.1, hrow.2.2.2⟩
  }

/-! ## Replacement load on an ascending braid row -/

/-- On an ascending interior row, every positive parked-only value below
the left MEX must be replaced at the right source.  Since it is not the
fresh left output, the only possible replacement channels are the newly
available diagonal owner at `r` or the genuinely new column tail at `r`. -/
theorem r173_allAscent_interior_parked_replacement
    {v r g a t z : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (hat : a < t)
    (htv : t < v)
    (hascent : gameF t (r - 1) < gameF t r)
    (hzpos : 0 < z)
    (hzlt : z < gameF t (r - 1))
    (hpark : ParkedOnly gameF t (r - 1) z) :
    (r < t /\ gameF r r = z) \/
      ColTail gameF t r z := by
  have hrow := hbraid.interiorHighBraid t hat htv
  have hrightSource : B gameF t r z :=
    hrow.2.2.1.2.2 z hzpos (by omega)
  have hrpos : 0 < r := by
    have hfailure := hbraid.failure
    omega
  have hrsucc : (r - 1) + 1 = r := by omega
  have hnext : B gameF t ((r - 1) + 1) z := by
    simpa only [hrsucc] using hrightSource
  rcases (parked_value_next_source_exact hpark).mp hnext with
      hdiag | htail | hfresh
  · left
    simpa only [hrsucc] using hdiag
  · right
    simpa only [hrsucc] using htail
  · have heq : gameF t (r - 1) = z := hfresh
    omega

/-- A non-circular remaining atom: an all-ascent failed braid must expose a
parked value below the left strand which has neither possible replacement
on the right.  Unlike the R172 right-history atom, its conclusion is not
universally forbidden and it pinpoints the required global capacity debt. -/
def R173AllAscentBraidHasUnreplacedParkedWitness : Prop :=
  forall {v r g a : Nat},
    FailedTerminalDeepHistoryHighBraidPacket v r g a ->
    (forall t, a <= t -> t < v ->
      gameF t (r - 1) < gameF t r) ->
    exists t z,
      a < t /\
      t < v /\
      0 < z /\
      z < gameF t (r - 1) /\
      ParkedOnly gameF t (r - 1) z /\
      Not (r < t /\ gameF r r = z) /\
      Not (ColTail gameF t r z)

/-- The unreplaced-witness atom closes the all-ascent branch immediately by
the exact replacement theorem. -/
theorem r173_noAllInteriorAscentFailedBraid_of_unreplacedParkedWitness
    (hwitness : R173AllAscentBraidHasUnreplacedParkedWitness) :
    R173NoAllInteriorAscentFailedTerminalHighBraid := by
  intro v r g a hbraid hascent
  rcases hwitness hbraid hascent with
    ⟨t, z, hat, htv, hzpos, hzlt, hpark, hnoDiag, hnoTail⟩
  have hasc := hascent t (Nat.le_of_lt hat) htv
  rcases r173_allAscent_interior_parked_replacement
      hbraid hat htv hasc hzpos hzlt hpark with hdiag | htail
  · exact hnoDiag hdiag
  · exact hnoTail htail

#print axioms r173_terminalFreeze_rightHistory_empty
#print axioms r173_relayForcesRightHistory_iff_noAllInteriorAscentFailedBraid
#print axioms r173_terminalFreeze_relayTrajectory
#print axioms r173_failedTerminalHighBraid_interior_targetChannels
#print axioms r173_allAscent_interior_parked_replacement
#print axioms r173_noAllInteriorAscentFailedBraid_of_unreplacedParkedWitness

end ChompLean
