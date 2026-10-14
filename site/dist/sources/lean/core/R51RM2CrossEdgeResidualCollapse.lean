import R51RM2ExactResidualAudit
import R51EventEMaximalBulkFrozenCarry

set_option autoImplicit false

namespace ChompLean

/-!
R51 strengthened RM2 audit after cross-edge owner packing.

Under UnitDip, an RM2 counterexample is now exactly one of only two
residuals: a nonmaximal event E carrying the global cross-edge inequality,
or a maximal event E carrying a linear-size family of completed frozen
row-start values.
-/

def NonmaxMarginEventECrossEdgeResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  MarginEventECounterexample s /\
  EventEDefectPacketInvariant s d delta z /\
  delta + 5 <= s /\
  exists c b0, EventECrossEdgeSurvivorCertificate s delta z c b0

def MaximalMarginEventEBulkFrozenResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  MarginEventECounterexample s /\
  delta + 4 = s /\
  exists c b0,
    EventEMaximalBulkFrozenCarryCertificate s delta z c b0

/-- Exact two-residual form of RM2 failure under UnitDip. -/
theorem gameF_unitDip_not_RM2_iff_cross_edge_residuals
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      (exists s, NonmaxMarginEventECrossEdgeResidual s) \/
      (exists s, MaximalMarginEventEBulkFrozenResidual s) := by
  constructor
  · intro hNotRM2
    rcases (gameF_unitDip_not_RM2_iff_exists_eventE hU).mp hNotRM2 with
      ⟨s, hEvent⟩
    rcases hEvent with ⟨hdip, hmargin, hnextDip⟩
    have hEvent' : MarginEventECounterexample s :=
      ⟨hdip, hmargin, hnextDip⟩
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    have hInv := gameF_margin_eventE_parametric_defect_invariant
      hU hdip hmargin hnextDip
    change EventEDefectPacketInvariant s d delta z at hInv
    by_cases hmax : delta + 4 = s
    · right
      have hbulk := gameF_margin_eventE_maximal_defect_bulk_frozen_carries
        hU hdip hmargin hnextDip hmax
      change exists c b0,
        EventEMaximalBulkFrozenCarryCertificate s delta z c b0 at hbulk
      exact ⟨s, hEvent', hmax, hbulk⟩
    · left
      have hcross := gameF_margin_eventE_cross_edge_survivor_bound
        hU hdip hmargin hnextDip
      change exists c b0,
        EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
      have hnonmax : delta + 5 <= s := by
        have hupper := hInv.2.1
        omega
      exact ⟨s, hEvent', hInv, hnonmax, hcross⟩
  · intro hResidual
    apply (gameF_unitDip_not_RM2_iff_exists_eventE hU).mpr
    rcases hResidual with hNonmax | hMax
    · rcases hNonmax with ⟨s, hres⟩
      exact ⟨s, hres.1⟩
    · rcases hMax with ⟨s, hres⟩
      exact ⟨s, hres.1⟩

/-- Positive RM2 formulation: it is enough, and under UnitDip necessary,
to exclude the two strengthened cross-edge residuals. -/
theorem gameF_unitDip_RM2_iff_no_cross_edge_residuals
    (hU : UnitDip gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel <->
      (Not (exists s, NonmaxMarginEventECrossEdgeResidual s) /\
       Not (exists s, MaximalMarginEventEBulkFrozenResidual s)) := by
  constructor
  · intro hRM2
    constructor
    · intro hNonmax
      have hNotRM2 :=
        (gameF_unitDip_not_RM2_iff_cross_edge_residuals hU).mpr
          (Or.inl hNonmax)
      exact hNotRM2 hRM2
    · intro hMax
      have hNotRM2 :=
        (gameF_unitDip_not_RM2_iff_cross_edge_residuals hU).mpr
          (Or.inr hMax)
      exact hNotRM2 hRM2
  · rintro ⟨hNoNonmax, hNoMax⟩
    apply Classical.byContradiction
    intro hNotRM2
    rcases (gameF_unitDip_not_RM2_iff_cross_edge_residuals hU).mp
        hNotRM2 with hNonmax | hMax
    · exact hNoNonmax hNonmax
    · exact hNoMax hMax

#print axioms gameF_unitDip_not_RM2_iff_cross_edge_residuals
#print axioms gameF_unitDip_RM2_iff_no_cross_edge_residuals

end ChompLean
