import R59Q4FiniteFateCollapse
import R57ExactResidualAudit

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
R60: lift the R59 Q4 collapse to the exact RM2 residual.

The first three R55 branches are retained verbatim.  The fourth branch now
uses `EventEFourPrefixFiniteFateR59`, so its loss arm has only an early
owner.  The equivalence below is conditional on the same `UnitDip`
hypothesis as the R55 reduction; no new closure assumption is introduced.
-/

def EventEFourPrefixFiniteFateGeometryCertificateR59
    (s delta z c b0 : Nat) : Prop :=
  EventENonDipStrictSharedOwnerCertificate s delta z c b0 /\
  exists g,
    g ∈ EventEFourPrefixBandSlots s delta c b0 /\
    EventEFourPrefixFiniteFateR59 s delta z g

theorem eventE_four_prefix_geometry_iff_R59
    (hU : UnitDip gameRecurrenceModel)
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    let z := gameF (s + 1) (s + 1) - 1
    EventEFourPrefixFiniteFateGeometryCertificate
        s delta z c b0 <->
      EventEFourPrefixFiniteFateGeometryCertificateR59
        s delta z c b0 := by
  dsimp only
  let delta := 2 * s - gameF (s + 1) (s + 1)
  let z := gameF (s + 1) (s + 1) - 1
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventEFourPrefixFiniteFateGeometryCertificate s delta z c b0 <->
    EventEFourPrefixFiniteFateGeometryCertificateR59 s delta z c b0
  constructor
  · rintro ⟨hstrict, g, hg, hfate⟩
    have hiff := eventE_four_prefix_finite_fate_iff_R59
      hU hres hcross hstrict hg
    change EventEFourPrefixFiniteFate s z g <->
      EventEFourPrefixFiniteFateR59 s delta z g at hiff
    exact ⟨hstrict, g, hg, hiff.mp hfate⟩
  · rintro ⟨hstrict, g, hg, hfate⟩
    have hiff := eventE_four_prefix_finite_fate_iff_R59
      hU hres hcross hstrict hg
    change EventEFourPrefixFiniteFate s z g <->
      EventEFourPrefixFiniteFateR59 s delta z g at hiff
    exact ⟨hstrict, g, hg, hiff.mpr hfate⟩

def EventER59ExactGeometricTerminal
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBandHitLeftHistoryCertificate s delta z c b0 \/
  EventEThirdDipBoundaryEchoLedgerTerminal s delta z c b0 \/
  EventEDeepQuietExactGeometryCertificate s delta z c b0 \/
  EventEFourPrefixFiniteFateGeometryCertificateR59 s delta z c b0

theorem eventE_R55_exact_terminal_iff_R59
    (hU : UnitDip gameRecurrenceModel)
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    let z := gameF (s + 1) (s + 1) - 1
    EventER55ExactGeometricTerminal s delta z c b0 <->
      EventER59ExactGeometricTerminal s delta z c b0 := by
  dsimp only
  let delta := 2 * s - gameF (s + 1) (s + 1)
  let z := gameF (s + 1) (s + 1) - 1
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  have hfour := eventE_four_prefix_geometry_iff_R59 hU hres hcross
  change EventEFourPrefixFiniteFateGeometryCertificate s delta z c b0 <->
    EventEFourPrefixFiniteFateGeometryCertificateR59 s delta z c b0
    at hfour
  constructor
  · intro hterm
    rcases hterm with hhit | hboundary | hdeep | hq4
    · exact Or.inl hhit
    · exact Or.inr (Or.inl hboundary)
    · exact Or.inr (Or.inr (Or.inl hdeep))
    · exact Or.inr (Or.inr (Or.inr (hfour.mp hq4)))
  · intro hterm
    rcases hterm with hhit | hboundary | hdeep | hq4
    · exact Or.inl hhit
    · exact Or.inr (Or.inl hboundary)
    · exact Or.inr (Or.inr (Or.inl hdeep))
    · exact Or.inr (Or.inr (Or.inr (hfour.mpr hq4)))

def NonmaxMarginEventER59ExactGeometricResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  NonmaxMarginEventECrossEdgeResidual s /\
  2 * delta + 10 <= s /\
  exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 /\
    EventER59ExactGeometricTerminal s delta z c b0

theorem R55_exact_residual_iff_R59
    (hU : UnitDip gameRecurrenceModel) {s : Nat} :
    NonmaxMarginEventER55ExactGeometricResidual s <->
      NonmaxMarginEventER59ExactGeometricResidual s := by
  dsimp [NonmaxMarginEventER55ExactGeometricResidual,
    NonmaxMarginEventER59ExactGeometricResidual]
  constructor
  · rintro ⟨hres, henv, c, b0, hcross, hterm⟩
    have hiff := eventE_R55_exact_terminal_iff_R59
      hU hres hcross
    exact ⟨hres, henv, c, b0, hcross, hiff.mp hterm⟩
  · rintro ⟨hres, henv, c, b0, hcross, hterm⟩
    have hiff := eventE_R55_exact_terminal_iff_R59
      hU hres hcross
    exact ⟨hres, henv, c, b0, hcross, hiff.mpr hterm⟩

theorem gameF_unitDip_not_RM2_iff_R59_exact_geometric_residual
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      exists s, NonmaxMarginEventER59ExactGeometricResidual s := by
  rw [gameF_unitDip_not_RM2_iff_R55_exact_geometric_residual hU]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, (R55_exact_residual_iff_R59 hU).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (R55_exact_residual_iff_R59 hU).mpr hs⟩

theorem gameF_unitDip_RM2_iff_no_R59_exact_geometric_residual
    (hU : UnitDip gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel <->
      Not (exists s, NonmaxMarginEventER59ExactGeometricResidual s) := by
  constructor
  · intro hRM2 hresidual
    exact ((gameF_unitDip_not_RM2_iff_R59_exact_geometric_residual hU).mpr
      hresidual) hRM2
  · intro hno
    apply Classical.byContradiction
    intro hnot
    exact hno
      ((gameF_unitDip_not_RM2_iff_R59_exact_geometric_residual hU).mp hnot)

#print axioms eventE_four_prefix_geometry_iff_R59
#print axioms eventE_R55_exact_terminal_iff_R59
#print axioms R55_exact_residual_iff_R59
#print axioms gameF_unitDip_not_RM2_iff_R59_exact_geometric_residual
#print axioms gameF_unitDip_RM2_iff_no_R59_exact_geometric_residual

end ChompLean
