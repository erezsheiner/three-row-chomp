import R55LeftHistoryBandHitClosure
import R55BoundaryEchoLedgerClosure
import R55DeepQuietEchoLedgerClosure
import R55BandHitFourthClosure

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
R55 exact geometric terminal reduction.

The overlap envelope removes the old *high-defect selector* used to create
R53's fourth disjunct.  It does not say that the four-prefix list is empty.
Accordingly the no-third-dip branch is split exactly into

* a chosen four-prefix value together with its finite fate, or
* the genuinely empty-four deep-quiet geometry.

Thus the terminal menu below preserves all geometric subcases while deleting
only the redundant high-defect atom.
-/

/-- The deep-quiet branch with both exact global echo descriptions attached:
the canonical band exhausts the old echo ledger, and its upper tail is the
complete south-west successor staircase up to the two packet columns. -/
def EventEDeepQuietExactGeometryCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventENonDipDeepQuietTerminalCertificate s delta z c b0 /\
  (EventEDeepQuietBandValues s delta c b0).Perm
    (PastDiagonalEchoValues s) /\
  EventEDeepQuietNearPerfectOwnerMatching s delta c b0 /\
  ((c = s - 1 /\ gameF s (s - 1) = z + 1 /\
      (forall g, b0 < g -> g < s - 1 ->
        gameF (g + 1) (g + 1) = gameF s g)) \/
   (b0 = s - 1 /\ gameF s (s - 1) = z /\
      (exists a, c < a /\ a < s /\ gameF a c = z) /\
      (forall g, c < g -> g < s - 1 ->
        gameF (g + 1) (g + 1) = gameF s g)))

/-- The surviving `Q4` branch is geometric rather than a new high-defect
atom: one actual fourth-prefix slot is selected and its finite fate is
recorded. -/
def EventEFourPrefixFiniteFateGeometryCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventENonDipStrictSharedOwnerCertificate s delta z c b0 /\
  exists g,
    g ∈ EventEFourPrefixBandSlots s delta c b0 /\
    EventEFourPrefixFiniteFate s z g

/-- The exact four-way geometric menu after importing LEFT-HISTORY, the
boundary echo ledger, the complete deep-quiet staircase, and finite Q4
fate. -/
def EventER55ExactGeometricTerminal
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBandHitLeftHistoryCertificate s delta z c b0 \/
  EventEThirdDipBoundaryEchoLedgerTerminal s delta z c b0 \/
  EventEDeepQuietExactGeometryCertificate s delta z c b0 \/
  EventEFourPrefixFiniteFateGeometryCertificate s delta z c b0

/-- The global ENV inequality carried by every nonmaximal Event E. -/
theorem gameF_nonmax_eventE_R55_env_bound
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    2 * delta + 10 <= s := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta (d - 1) /\ _ at hresData
  rcases hresData.1 with ⟨hdip0, hmargin, hdip1⟩
  have henv := gameF_margin_eventE_second_dip_env_defect_bound
    hU hdip0 hmargin hdip1
  change delta + (s + 3) / 2 + 4 <= s /\
      2 * delta + 10 <= s at henv
  exact henv.2

/-- ENV rules out the old R53 high-defect selector everywhere in a
nonmaximal Event E.  This is the precise sense in which the old fourth
*atom* disappears; it makes no assertion that `Q4` itself is empty. -/
theorem gameF_nonmax_eventE_old_high_defect_selector_impossible
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    Not (s < 2 * delta + 7) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  change Not (s < 2 * delta + 7)
  have henv := gameF_nonmax_eventE_R55_env_bound hU hres
  change 2 * delta + 10 <= s at henv
  intro hbad
  apply (Nat.not_lt_of_ge ?_) hbad
  exact Nat.le_trans
    (Nat.add_le_add_left (by decide : 7 <= 10) (2 * delta)) henv

/-- Construction of the exact deep-quiet geometry from the terminal core. -/
theorem gameF_nonmax_eventE_deep_quiet_exact_geometry
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventEDeepQuietExactGeometryCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  let delta := 2 * s - gameF (s + 1) (s + 1)
  let z := gameF (s + 1) (s + 1) - 1
  have hperm := gameF_deep_quiet_band_values_perm_all_old_echoes
    hU hres hcross hterm
  change (EventEDeepQuietBandValues s delta c b0).Perm
    (PastDiagonalEchoValues s) at hperm
  have hmatching := gameF_deep_quiet_near_perfect_forward_owner_matching
    hU hres hcross hterm
  change EventEDeepQuietNearPerfectOwnerMatching
    s delta c b0 at hmatching
  have htail :=
    gameF_deep_quiet_complete_southwest_staircase_to_tail_packet
      hU hres hcross hterm
  change
    (c = s - 1 /\ gameF s (s - 1) = z + 1 /\
      (forall g, b0 < g -> g < s - 1 ->
        gameF (g + 1) (g + 1) = gameF s g)) \/
    (b0 = s - 1 /\ gameF s (s - 1) = z /\
      (exists a, c < a /\ a < s /\ gameF a c = z) /\
      (forall g, c < g -> g < s - 1 ->
        gameF (g + 1) (g + 1) = gameF s g)) at htail
  exact ⟨hterm, hperm, hmatching, htail⟩

/-- Exact no-third-dip split.  Under ENV, the strict shared-owner core is
equivalent to the disjoint geometric alternatives `Q4` inhabited versus
`Q4` empty/deep.  This explicitly retains `Q4` after deleting the old R53
high-defect selector. -/
theorem eventE_nondip_q4_fate_or_deep_geometry_iff_strict
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (henv : 2 * (2 * s - gameF (s + 1) (s + 1)) + 10 <= s) :
    (EventEFourPrefixFiniteFateGeometryCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0 \/
      EventEDeepQuietExactGeometryCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0) <->
    EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  let delta := 2 * s - gameF (s + 1) (s + 1)
  let z := gameF (s + 1) (s + 1) - 1
  change
    (EventEFourPrefixFiniteFateGeometryCertificate s delta z c b0 \/
      EventEDeepQuietExactGeometryCertificate s delta z c b0) <->
    EventENonDipStrictSharedOwnerCertificate s delta z c b0
  change 2 * delta + 10 <= s at henv
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  constructor
  · rintro (hQ4 | hdeep)
    · exact hQ4.1
    · exact hdeep.1.1
  · intro hstrict
    have hsplit := eventE_nondip_quiet_strict_owner_reduction
      hstrict (by omega : 2 * delta + 7 <= s)
    rcases hsplit with ⟨g, hg⟩ | hdeep
    · left
      exact ⟨hstrict, g, hg,
        eventE_four_prefix_value_finite_fate hcross hg⟩
    · right
      exact gameF_nonmax_eventE_deep_quiet_exact_geometry
        hU hres hcross hdeep

/-- Every nonmaximal Event E reaches one of the four exact geometric
terminals.  The proof uses the genuine R53 three-way trichotomy; ENV is used
only to make the no-dip Q4/deep split exhaustive. -/
theorem gameF_nonmax_eventE_R55_exact_geometric_terminals
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 /\
      EventER55ExactGeometricTerminal s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have htri := gameF_nonmax_eventE_R53_shared_owner_trichotomy hU hres
  change exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 /\
      (EventEThirdDipPenultimateHitCertificate s delta z c b0 \/
       EventEThirdDipExtraForbiddenCertificate s delta z c b0 \/
       EventENonDipSharedOwnerSaturationCertificate s delta z c b0)
    at htri
  rcases htri with ⟨c, b0, hcross, hhit | hextra | hnondip⟩
  · have hcompressed :=
      gameF_nonmax_eventE_third_dip_band_hit_compressed
        hU hres hcross hhit
    have hleft := gameF_nonmax_eventE_third_dip_band_hit_left_history
      hU hres hcross hcompressed
    exact ⟨c, b0, hcross, Or.inl hleft⟩
  · have hboundary :=
      gameF_nonmax_eventE_third_dip_extra_boundary_saturation
        hU hres hcross hextra
    have hledger := gameF_nonmax_eventE_boundary_echo_ledger_terminal
      hU hres hboundary
    exact ⟨c, b0, hcross, Or.inr (Or.inl hledger)⟩
  · have hstrict :=
      gameF_nonmax_eventE_nondip_strict_shared_owner_saturation
        hU hres hcross hnondip.1
    change EventENonDipStrictSharedOwnerCertificate
      s delta z c b0 at hstrict
    have hresData := hres
    change MarginEventECounterexample s /\
        EventEDefectPacketInvariant s d delta z /\ _ at hresData
    rcases hresData.1 with ⟨hdip0, hmargin, hdip1⟩
    have henv := gameF_margin_eventE_second_dip_env_defect_bound
      hU hdip0 hmargin hdip1
    change delta + (s + 3) / 2 + 4 <= s /\
        2 * delta + 10 <= s at henv
    have hsplit :=
      (eventE_nondip_q4_fate_or_deep_geometry_iff_strict
        hU hres hcross henv.2).2 hstrict
    rcases hsplit with hQ4 | hdeep
    · exact ⟨c, b0, hcross,
        Or.inr (Or.inr (Or.inr hQ4))⟩
    · exact ⟨c, b0, hcross,
        Or.inr (Or.inr (Or.inl hdeep))⟩

def NonmaxMarginEventER55ExactGeometricResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  NonmaxMarginEventECrossEdgeResidual s /\
  2 * delta + 10 <= s /\
  exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 /\
    EventER55ExactGeometricTerminal s delta z c b0

/-- Exact preservation theorem: under UnitDip, RM2 fails iff one of the
four explicit geometric terminals exists. -/
theorem gameF_unitDip_not_RM2_iff_R55_exact_geometric_residual
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      exists s, NonmaxMarginEventER55ExactGeometricResidual s := by
  constructor
  · intro hNotRM2
    rcases (gameF_unitDip_not_RM2_iff_R53_nonmax_finite_residual hU).mp
        hNotRM2 with ⟨s, hR53⟩
    have hres : NonmaxMarginEventECrossEdgeResidual s := hR53.1
    have hgeo := gameF_nonmax_eventE_R55_exact_geometric_terminals hU hres
    have henv := gameF_nonmax_eventE_R55_env_bound hU hres
    exact ⟨s, hres, henv, hgeo⟩
  · rintro ⟨s, hres⟩
    apply (gameF_unitDip_not_RM2_iff_exists_eventE hU).mpr
    exact ⟨s, hres.1.1⟩

/-- Positive dual of the exact geometric reduction. -/
theorem gameF_unitDip_RM2_iff_no_R55_exact_geometric_residual
    (hU : UnitDip gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel <->
      Not (exists s, NonmaxMarginEventER55ExactGeometricResidual s) := by
  constructor
  · intro hRM2 hResidual
    exact ((gameF_unitDip_not_RM2_iff_R55_exact_geometric_residual hU).mpr
      hResidual) hRM2
  · intro hNoResidual
    apply Classical.byContradiction
    intro hNotRM2
    exact hNoResidual
      ((gameF_unitDip_not_RM2_iff_R55_exact_geometric_residual hU).mp
        hNotRM2)

#print axioms gameF_nonmax_eventE_old_high_defect_selector_impossible
#print axioms gameF_nonmax_eventE_R55_env_bound
#print axioms gameF_nonmax_eventE_deep_quiet_exact_geometry
#print axioms eventE_nondip_q4_fate_or_deep_geometry_iff_strict
#print axioms gameF_nonmax_eventE_R55_exact_geometric_terminals
#print axioms gameF_unitDip_not_RM2_iff_R55_exact_geometric_residual
#print axioms gameF_unitDip_RM2_iff_no_R55_exact_geometric_residual

end ChompLean
