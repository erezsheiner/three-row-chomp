import R33UnitDipFirstGapTrichotomy
import R34MarginEventEEquivalence

set_option autoImplicit false

namespace ChompLean

/-!
Consolidated local interface for RM2.

The global-looking hypotheses `UnitDip` and `MarginZRehost` are replaced by
four explicit local obstruction exclusions: three mutually exclusive
first-gap species for a deep dip, and the immediate event-E recapture at a
numerical-margin unit dip.
-/

/-- All three exact first-gap obstructions to `UnitDip` are absent. -/
def NoDipFirstGapObstructions (M : RecurrenceModel) : Prop :=
  ∀ s,
    ¬ DipFirstGapPastDiagonal M s ∧
    ¬ DipFirstGapFutureDiagonalLoss M s ∧
    ¬ DipFirstGapLateBlockerLoss M s

/-- The complete local package isolated by the RM2 audit. -/
def RM2LocalObstructionPackage (M : RecurrenceModel) : Prop :=
  NoDipFirstGapObstructions M ∧ MarginNoConsecutiveDips M

/-- The first three local exclusions are exactly `UnitDip`. -/
theorem noDipFirstGapObstructions_iff_unitDip (M : RecurrenceModel) :
    NoDipFirstGapObstructions M ↔ UnitDip M := by
  rw [unitDip_iff_no_first_gap_obstructions]
  rfl

/-- Main consolidated reduction: the four local obstruction exclusions
imply the two-step diagonal record law. -/
theorem twoStepRecordLaw_of_local_obstruction_package
    (M : RecurrenceModel) (hLocal : RM2LocalObstructionPackage M) :
    TwoStepDiagonalRecordLaw M := by
  have hU : UnitDip M :=
    (noDipFirstGapObstructions_iff_unitDip M).1 hLocal.1
  intro i a hia
  exact twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
    M hU hLocal.2 hia

/-- Expanded hypothesis form, convenient for downstream files. -/
theorem twoStepRecordLaw_of_four_local_exclusions
    (M : RecurrenceModel)
    (hFirstGap : ∀ s,
      ¬ DipFirstGapPastDiagonal M s ∧
      ¬ DipFirstGapFutureDiagonalLoss M s ∧
      ¬ DipFirstGapLateBlockerLoss M s)
    (hEventE : MarginNoConsecutiveDips M) :
    TwoStepDiagonalRecordLaw M :=
  twoStepRecordLaw_of_local_obstruction_package M ⟨hFirstGap, hEventE⟩

/-- Actual-game specialization. -/
theorem game_twoStepRecordLaw_of_local_obstruction_package
    (hLocal : RM2LocalObstructionPackage gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel :=
  twoStepRecordLaw_of_local_obstruction_package gameRecurrenceModel hLocal

#print axioms twoStepRecordLaw_of_local_obstruction_package
#print axioms game_twoStepRecordLaw_of_local_obstruction_package

end ChompLean
