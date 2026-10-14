import R52RM2BulkFrozenSevenAtomResidual
import R52NonmaxEventEThirdEdgePropagation
import R52EventEMaximalSurvivorDiagonalSqueeze
import R52EventEFrozenCarryStaircase

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R52 final integration: propagate the nonmaximal residual through a third
edge, and saturate the maximal residual simultaneously by the exact
diagonal/row-start count, the seven high configurations, and the frozen
cutoff staircase.
-/

def NonmaxMarginEventER52PropagatedResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  NonmaxMarginEventECrossEdgeResidual s /\
  exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 /\
    (EventEThirdDipPenultimateHitCertificate s delta z c b0 \/
     EventEThirdDipExtraForbiddenCertificate s delta z c b0 \/
     EventENonDipHighLossPacketCertificate s delta z c b0)

def MaximalMarginEventER52SaturatedResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  MaximalMarginEventEBulkFrozenResidual s /\
  (exists c b0,
    EventEMaximalBulkSevenAtomCertificate s delta z c b0) /\
  (exists c b0,
    EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z c b0 /\
    (EventETriplePrefixBandSlots s delta c b0).length = s / 2 /\
    (EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length + 4 =
        (s + 1) / 2) /\
  forall t, t <= s -> exists c b0,
    EventEMaximalFrozenCarryStaircaseCertificate s delta z c b0 t

/-- Under UnitDip, RM2 failure is exactly the propagated nonmaximal
residual or the fully saturated maximal residual. -/
theorem gameF_unitDip_not_RM2_iff_R52_saturated_propagation_residuals
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      (exists s, NonmaxMarginEventER52PropagatedResidual s) \/
      (exists s, MaximalMarginEventER52SaturatedResidual s) := by
  constructor
  · intro hNotRM2
    rcases (gameF_unitDip_not_RM2_iff_cross_edge_residuals hU).mp
        hNotRM2 with hNonmax | hMax
    · left
      rcases hNonmax with ⟨s, hres⟩
      have hprop := gameF_nonmax_eventE_third_edge_propagation_trichotomy
        hU hres
      exact ⟨s, hres, hprop⟩
    · right
      rcases hMax with ⟨s, hres⟩
      have hEvent := hres.1
      have hmax := hres.2.1
      rcases hEvent with ⟨hdip, hmargin, hnextDip⟩
      have hEvent' : MarginEventECounterexample s :=
        ⟨hdip, hmargin, hnextDip⟩
      let d := gameF (s + 1) (s + 1)
      let delta := 2 * s - d
      let z := d - 1
      have hSeven := gameF_margin_eventE_maximal_R52_bulk_seven_atom_residual
        hU hdip hmargin hnextDip hmax
      change exists c b0,
        EventEMaximalBulkSevenAtomCertificate s delta z c b0 at hSeven
      have hExact := gameF_margin_eventE_maximal_survivor_count_exact
        hU hdip hmargin hnextDip hmax
      change exists c b0,
        EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z c b0 /\
        (EventETriplePrefixBandSlots s delta c b0).length = s / 2
        at hExact
      rcases hExact with ⟨ce, be, hSqueeze, hTriple⟩
      have hMissing := gameF_margin_eventE_maximal_missing_total_exact
        hU hdip hmargin hnextDip hmax
      change exists c b0,
        EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z c b0 /\
        (EventEMissingBandSlots s delta c b0).length +
          (EventESecondMissingBandSlots s delta c b0).length + 4 =
            (s + 1) / 2 at hMissing
      rcases hMissing with ⟨cm, bm, hSqueezeM, hMissingEq⟩
      have hceEq : ce = cm := by
        have hbaseE := hSqueeze.1.1.1.1
        have hbaseM := hSqueezeM.1.1.1.1
        rcases hbaseE with
          ⟨hce, _hbe, _hneE, hSuccE, _restE⟩
        rcases hbaseM with
          ⟨hcm, _hbm, _hneM, hSuccM, _restM⟩
        exact gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hce) (Nat.le_of_lt hcm)
          (hSuccE.trans hSuccM.symm)
      have hbeEq : be = bm := by
        have hbaseE := hSqueeze.1.1.1.1
        have hbaseM := hSqueezeM.1.1.1.1
        rcases hbaseE with
          ⟨_hce, hbe, _hneE, _hSuccE, hBaseE, _restE⟩
        rcases hbaseM with
          ⟨_hcm, hbm, _hneM, _hSuccM, hBaseM, _restM⟩
        exact gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hbe) (Nat.le_of_lt hbm)
          (hBaseE.trans hBaseM.symm)
      subst cm
      subst bm
      have hStairs : forall t, t <= s -> exists c b0,
          EventEMaximalFrozenCarryStaircaseCertificate
            s delta z c b0 t := by
        intro t hts
        exact gameF_margin_eventE_maximal_defect_frozen_carry_staircase
          hU hdip hmargin hnextDip hts hmax
      exact ⟨s, ⟨hEvent', hmax, hres.2.2⟩,
        hSeven, ⟨ce, be, hSqueeze, hTriple, hMissingEq⟩, hStairs⟩
  · intro hResidual
    apply (gameF_unitDip_not_RM2_iff_cross_edge_residuals hU).mpr
    rcases hResidual with hNonmax | hMax
    · rcases hNonmax with ⟨s, hres⟩
      exact Or.inl ⟨s, hres.1⟩
    · rcases hMax with ⟨s, hres⟩
      exact Or.inr ⟨s, hres.1⟩

/-- Positive form of the final R52 reduction. -/
theorem gameF_unitDip_RM2_iff_no_R52_saturated_propagation_residuals
    (hU : UnitDip gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel <->
      (Not (exists s, NonmaxMarginEventER52PropagatedResidual s) /\
       Not (exists s, MaximalMarginEventER52SaturatedResidual s)) := by
  constructor
  · intro hRM2
    constructor
    · intro hNonmax
      exact
        ((gameF_unitDip_not_RM2_iff_R52_saturated_propagation_residuals
          hU).mpr (Or.inl hNonmax)) hRM2
    · intro hMax
      exact
        ((gameF_unitDip_not_RM2_iff_R52_saturated_propagation_residuals
          hU).mpr (Or.inr hMax)) hRM2
  · rintro ⟨hNoNonmax, hNoMax⟩
    apply Classical.byContradiction
    intro hNotRM2
    rcases
        (gameF_unitDip_not_RM2_iff_R52_saturated_propagation_residuals
          hU).mp hNotRM2 with hNonmax | hMax
    · exact hNoNonmax hNonmax
    · exact hNoMax hMax

#print axioms gameF_unitDip_not_RM2_iff_R52_saturated_propagation_residuals
#print axioms gameF_unitDip_RM2_iff_no_R52_saturated_propagation_residuals

end ChompLean
