import R54DeepQuietSchedulerExclusion
import R54RM2DefectGapTerminalReduction

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R55: full-encoding geometry of the deep quiet Event-E terminal.

The pointwise three-ride geometry is not itself contradictory: a past
diagonal value can legally be re-emitted on several later rows in distinct
columns and then disappear.  The useful full-game input is instead the
following forward-owner principle.  If a value from an old row is below a
later diagonal and absent from that later strict prefix, exact diagonal MEX
gives a past diagonal owner.  Encoding non-attack forces that owner to lie
strictly to the right of the old host column.

In a genuine deep-quiet Event E every canonical band slot disappears on one
of the first three edges.  Applying the forward-owner principle at its first
missing row gives `g < owner(g) < s` for *every* band slot.  The last column
`s-1` therefore cannot be a band slot.  Since the band is the interval
`[s-delta-2,s)` with only `c,b0` removed, one of the two high packet columns
must be the last column.  If it is the `z` column, the packet-order theorem
forces an additional earlier ride of `z`.
-/

/-- A value lost before a later diagonal has a genuinely earlier diagonal
owner, and that owner lies strictly to the right of the old host column.

This is a full `Encodes gameF` statement: the strict inequality `g<i` uses
both diagonal/general non-attack and the prohibition on re-emitting a
diagonal value later in its own lower column. -/
theorem gameF_lost_prefix_value_has_forward_past_diagonal_owner
    {s t g p : Nat}
    (hgs : g < s)
    (hhost : gameF s g = p)
    (hbelow : p < gameF t t)
    (hmissing : p ∉ StrictRowPrefixValues gameF t)
    (hnewDiagonals : forall i, s <= i -> i < t -> gameF i i ≠ p) :
    exists i, g < i /\ i < s /\ gameF i i = p := by
  have hpPos : 0 < p := by
    have hgt := gameRecurrenceModel.value_gt_index
      (q := s) (r := g) (Nat.le_of_lt hgs)
    change g < gameF s g at hgt
    rw [hhost] at hgt
    omega
  have hblocked : B gameF t t p :=
    (recurrence_diagonal_exact_mex gameRecurrenceModel t).2.2
      p hpPos hbelow
  have hR : R gameF t t p := by
    rcases hblocked with hR | hC
    · exact hR
    · exfalso
      apply hmissing
      exact mem_strictRowPrefixValues_iff_C.mpr hC
  rcases hR with ⟨i, hit, hownerRaw⟩
  have howner : gameF i i = p := by
    simpa [Nat.min_eq_left (Nat.le_of_lt hit)] using hownerRaw
  have his : i < s := by
    apply Nat.lt_of_not_ge
    intro hsi
    exact hnewDiagonals i hsi hit howner
  have hgi : g < i := by
    apply Nat.lt_of_not_ge
    intro hig
    by_cases hieq : i = g
    · subst i
      exact (encoding_diagonal_value_not_reemitted_in_owner_column
        game_encodes hgs) (hhost.trans howner.symm)
    · have higStrict : i < g := by omega
      exact gameRecurrenceModel.diagonal_general_no_attack
        higStrict (Nat.le_of_lt hgs) (howner.trans hhost.symm)
  exact ⟨i, hgi, his, howner⟩

/-- Full Event-E application: in the empty-four no-third-dip terminal,
every canonical defect-band slot has a past diagonal owner strictly between
the slot and the first event row.  This simultaneously handles values lost
on the first, second, or third edge. -/
theorem gameF_deep_quiet_every_band_slot_has_forward_owner
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    forall g, g ∈ EventEDefectBandSlots s delta c b0 ->
      exists i, g < i /\ i < s /\ gameF i i = gameF s g := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists ce be, EventECrossEdgeSurvivorCertificate s delta z ce be
    at hresData
  rcases hresData with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨hdip0, _hmargin, hdip1⟩
  have hzDiag1 : gameF (s + 1) (s + 1) = z + 1 := by
    have hz := hInv.2.2.2.1
    change z + 1 = d at hz
    omega
  have hunit0 := hU s hdip0
  change gameF (s + 1) (s + 1) + 1 = gameF s s at hunit0
  have hdiag0 : gameF s s = z + 2 := by omega
  have hunit1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hunit1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by omega
  have hnondip3 : Not
      (gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2)) :=
    hterm.1.1.1.1
  have hdiag3Lower : z <= gameF (s + 3) (s + 3) := by
    rw [hdiag2] at hnondip3
    omega
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      _hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  intro g hgBand
  have hgData := hslotsProps g hgBand
  have hgs : g < s := hgData.1
  have hpPos : 0 < gameF s g := by
    simpa [EventELowerTransition] using hgData.2.2.2.1
  have hpBelowZ : gameF s g < z := by
    simpa [EventELowerTransition] using hgData.2.2.2.2.1

  by_cases hrow1 : gameF s g ∈ StrictRowPrefixValues gameF (s + 1)
  · have hgSurv : g ∈ EventESurvivingBandSlots s delta c b0 := by
      apply List.mem_filter.mpr
      refine ⟨hgBand, ?_⟩
      simpa [EventESurvivingBandSlots] using hrow1
    by_cases hrow2 : gameF s g ∈ StrictRowPrefixValues gameF (s + 2)
    · have hgTriple : g ∈ EventETriplePrefixBandSlots s delta c b0 := by
        apply List.mem_filter.mpr
        refine ⟨hgSurv, ?_⟩
        simpa [EventETriplePrefixBandSlots] using hrow2
      have hrow3Missing : gameF s g ∉
          StrictRowPrefixValues gameF (s + 3) := by
        intro hrow3
        have hgFour : g ∈ EventEFourPrefixBandSlots s delta c b0 := by
          apply List.mem_filter.mpr
          refine ⟨hgTriple, ?_⟩
          simpa [EventEFourPrefixBandSlots] using hrow3
        rw [hterm.2.1] at hgFour
        simp at hgFour
      apply gameF_lost_prefix_value_has_forward_past_diagonal_owner
        (s := s) (t := s + 3) (g := g) (p := gameF s g)
        hgs rfl (by omega) hrow3Missing
      intro i hsi hi3 hEq
      have hiCases : i = s \/ i = s + 1 \/ i = s + 2 := by omega
      rcases hiCases with rfl | rfl | rfl
      · rw [hdiag0] at hEq
        omega
      · rw [hzDiag1] at hEq
        omega
      · rw [hdiag2] at hEq
        omega
    · have hrow2Missing : gameF s g ∉
          StrictRowPrefixValues gameF (s + 2) := hrow2
      apply gameF_lost_prefix_value_has_forward_past_diagonal_owner
        (s := s) (t := s + 2) (g := g) (p := gameF s g)
        hgs rfl (by omega) hrow2Missing
      intro i hsi hi2 hEq
      have hiCases : i = s \/ i = s + 1 := by omega
      rcases hiCases with rfl | rfl
      · rw [hdiag0] at hEq
        omega
      · rw [hzDiag1] at hEq
        omega
  · have hrow1Missing : gameF s g ∉
        StrictRowPrefixValues gameF (s + 1) := hrow1
    apply gameF_lost_prefix_value_has_forward_past_diagonal_owner
      (s := s) (t := s + 1) (g := g) (p := gameF s g)
      hgs rfl (by omega) hrow1Missing
    intro i hsi hi1 hEq
    have hiEq : i = s := by omega
    subst i
    rw [hdiag0] at hEq
    omega

/-- The full band-forward-owner geometry forces one of the two named high
packet cells to occupy the old row's last strict-prefix column. -/
theorem gameF_deep_quiet_forces_last_packet_column
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    c = s - 1 \/ b0 = s - 1 := by
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists ce be, EventECrossEdgeSurvivorCertificate s delta z ce be
    at hresData
  have hInv := hresData.2.1
  have hdeltaPos : 1 <= delta := hInv.1
  have hdeltaUpper : delta + 4 <= s := hInv.2.1
  by_cases hcLast : c = s - 1
  · exact Or.inl hcLast
  by_cases hbLast : b0 = s - 1
  · exact Or.inr hbLast
  exfalso
  have hlastRange : s - 1 ∈
      List.range' (s - delta - 2) (delta + 2) := by
    apply List.mem_range'_1.mpr
    constructor <;> omega
  have hlastEraseC : s - 1 ∈
      (List.range' (s - delta - 2) (delta + 2)).erase c := by
    exact (List.mem_erase_of_ne (Ne.symm hcLast)).mpr hlastRange
  have hlastBand : s - 1 ∈ EventEDefectBandSlots s delta c b0 := by
    change s - 1 ∈
      ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
    exact (List.mem_erase_of_ne (Ne.symm hbLast)).mpr hlastEraseC
  have hforward := gameF_deep_quiet_every_band_slot_has_forward_owner
    hU hres hcross hterm (s - 1) hlastBand
  rcases hforward with ⟨i, hlastI, hiS, _howner⟩
  omega

/-- Exact last-column normal form.  Either `z+1` is already the old `V1`,
or `z` is the old `V1` and the packet-order law forces a further earlier
ride of `z` in the `z+1` column. -/
theorem gameF_deep_quiet_last_column_or_extra_z_ride
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let z := gameF (s + 1) (s + 1) - 1
    (c = s - 1 /\ gameF s (s - 1) = z + 1) \/
      (b0 = s - 1 /\ gameF s (s - 1) = z /\
        exists a, c < a /\ a < s /\ gameF a c = z) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists ce be, EventECrossEdgeSurvivorCertificate s delta z ce be
    at hresData
  rcases hresData.1 with ⟨hdip0, hmargin, _hdip1⟩
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨hc, hb0, hcNe, hSucc, hBase,
      _hslotsNodup, _hslotsLen, _hslotsProps, _hweak⟩
  rcases gameF_deep_quiet_forces_last_packet_column
      hU hres hcross hterm with hcLast | hbLast
  · left
    subst c
    exact ⟨rfl, hSucc⟩
  · right
    have hzPos : 0 < z := by
      have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
      change s + 1 < d at hgt
      dsimp [z]
      omega
    have hsz : s < z := by
      have hInv := hresData.2.1
      have hsum := hInv.2.2.1
      have hzEq := hInv.2.2.2.1
      change d + delta = 2 * s at hsum
      change z + 1 = d at hzEq
      have hnonmax := hresData.2.2.1
      omega
    have hnotPast : forall a, a < s -> gameF a a ≠ z := by
      intro a has
      exact margin_guard_hole_not_past
        gameRecurrenceModel hdip0 hmargin a (by omega)
    have horder := consecutive_high_packet_order_or_prior_column_host
      gameRecurrenceModel hzPos hsz hc hb0 hSucc hBase hnotPast
    have hprior : exists a, c < a /\ a < s /\ gameF a c = z := by
      rcases horder with hbc | hprior
      · rw [hbLast] at hbc
        omega
      · exact hprior
    subst b0
    exact ⟨rfl, hBase, hprior⟩

/-- One more exact layer of the boundary normal form.  If the two high
packet cells are not precisely the last two strict-prefix columns (in one
of the two possible orders), then the penultimate band slot is forced to
be the immediate south-west echo of the diagonal at row `s-1`. -/
theorem gameF_deep_quiet_top_pair_or_penultimate_diagonal_echo
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let z := gameF (s + 1) (s + 1) - 1
    (c = s - 1 /\ b0 = s - 2 /\
      gameF s (s - 1) = z + 1 /\ gameF s (s - 2) = z) \/
    (b0 = s - 1 /\ c = s - 2 /\
      gameF s (s - 1) = z /\ gameF s (s - 2) = z + 1 /\
      exists a, s - 2 < a /\ a < s /\ gameF a (s - 2) = z) \/
    gameF (s - 1) (s - 1) = gameF s (s - 2) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists ce be, EventECrossEdgeSurvivorCertificate s delta z ce be
    at hresData
  have hInv := hresData.2.1
  have hdeltaPos : 1 <= delta := hInv.1
  have hdeltaUpper : delta + 4 <= s := hInv.2.1
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, hSucc, hBase,
      _hslotsNodup, _hslotsLen, _hslotsProps, _hweak⟩
  have hlast := gameF_deep_quiet_last_column_or_extra_z_ride
    hU hres hcross hterm
  rcases hlast with hSuccLast | hBaseLast
  · rcases hSuccLast with ⟨hcLast, hSuccAtLast⟩
    by_cases hbPenult : b0 = s - 2
    · left
      subst c
      subst b0
      exact ⟨rfl, rfl, hSuccAtLast, hBase⟩
    · right
      right
      have hpenultRange : s - 2 ∈
          List.range' (s - delta - 2) (delta + 2) := by
        apply List.mem_range'_1.mpr
        constructor <;> omega
      have hpenultEraseC : s - 2 ∈
          (List.range' (s - delta - 2) (delta + 2)).erase c := by
        have hne : s - 2 ≠ c := by
          rw [hcLast]
          omega
        exact (List.mem_erase_of_ne hne).mpr hpenultRange
      have hpenultBand : s - 2 ∈
          EventEDefectBandSlots s delta c b0 := by
        change s - 2 ∈
          ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
        exact (List.mem_erase_of_ne (Ne.symm hbPenult)).mpr hpenultEraseC
      rcases gameF_deep_quiet_every_band_slot_has_forward_owner
          hU hres hcross hterm (s - 2) hpenultBand with
        ⟨i, hpenultI, hiS, howner⟩
      have hi : i = s - 1 := by omega
      simpa [hi] using howner
  · rcases hBaseLast with ⟨hbLast, hBaseAtLast, a, hca, has, hride⟩
    by_cases hcPenult : c = s - 2
    · right
      left
      subst b0
      subst c
      exact ⟨rfl, rfl, hBaseAtLast, hSucc, a, hca, has, hride⟩
    · right
      right
      have hpenultRange : s - 2 ∈
          List.range' (s - delta - 2) (delta + 2) := by
        apply List.mem_range'_1.mpr
        constructor <;> omega
      have hpenultEraseC : s - 2 ∈
          (List.range' (s - delta - 2) (delta + 2)).erase c := by
        exact (List.mem_erase_of_ne (Ne.symm hcPenult)).mpr hpenultRange
      have hpenultBand : s - 2 ∈
          EventEDefectBandSlots s delta c b0 := by
        change s - 2 ∈
          ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
        have hne : s - 2 ≠ b0 := by
          rw [hbLast]
          omega
        exact (List.mem_erase_of_ne hne).mpr hpenultEraseC
      rcases gameF_deep_quiet_every_band_slot_has_forward_owner
          hU hres hcross hterm (s - 2) hpenultBand with
        ⟨i, hpenultI, hiS, howner⟩
      have hi : i = s - 1 := by omega
      simpa [hi] using howner

#print axioms gameF_lost_prefix_value_has_forward_past_diagonal_owner
#print axioms gameF_deep_quiet_every_band_slot_has_forward_owner
#print axioms gameF_deep_quiet_forces_last_packet_column
#print axioms gameF_deep_quiet_last_column_or_extra_z_ride
#print axioms gameF_deep_quiet_top_pair_or_penultimate_diagonal_echo

end ChompLean
