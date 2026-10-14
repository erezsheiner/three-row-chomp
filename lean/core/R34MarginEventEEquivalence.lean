import DipZRehostRM2IndependentAudit
import DipZRehostLandingGeometry

set_option autoImplicit false

namespace ChompLean

/-!
The numerical-margin service law needed by the strengthened RM2 reduction
has an exact event-E formulation.  Under `UnitDip`, it is equivalent to
excluding a consecutive dip only at the guarded numerical-margin sites.
This is weaker than a global no-consecutive-dips axiom.
-/

/-- No consecutive dip at precisely the numerical-margin sites used by
`MarginZRehost`. -/
def MarginNoConsecutiveDips (M : RecurrenceModel) : Prop :=
  ∀ s, M.f (s + 1) (s + 1) < M.f s s →
    (s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax M j < M.f (s + 1) (s + 1) - 1) →
    ¬ M.f (s + 2) (s + 2) < M.f (s + 1) (s + 1)

/-- A strict numerical margin rules out every diagonal owner of the dip
hole through the preceding row.  The immediately preceding diagonal is
excluded just by the dip inequality. -/
theorem margin_guard_hole_not_past
    (M : RecurrenceModel) {s : Nat}
    (hdip : M.f (s + 1) (s + 1) < M.f s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax M j < M.f (s + 1) (s + 1) - 1) :
    ∀ i, i ≤ s →
      M.f i i ≠ M.f (s + 1) (s + 1) - 1 := by
  intro i his hEq
  by_cases hiEq : i = s
  · subst i
    have hgt := M.diagonal_gt (s + 1)
    omega
  · have hisLt : i < s := by omega
    rcases hmargin with hs0 | ⟨j, hsj, hmargin⟩
    · omega
    · have hij : i ≤ j := by omega
      have hle := rmax_ge M j i hij
      rw [hEq] at hle
      omega

/-- Exact equivalence between numerical-margin service and exclusion of the
single immediate recapture event, assuming unit-depth dips. -/
theorem marginZRehost_iff_marginNoConsecutiveDips
    (M : RecurrenceModel) (hU : UnitDip M) :
    MarginZRehost M ↔ MarginNoConsecutiveDips M := by
  constructor
  · intro hZ s hdip hmargin
    let z := M.f (s + 1) (s + 1) - 1
    have hzPos : 0 < z := by
      dsimp [z]
      have hgt := M.diagonal_gt (s + 1)
      omega
    have hdiagHole : M.f (s + 1) (s + 1) = z + 1 := by
      dsimp [z]
      have hgt := M.diagonal_gt (s + 1)
      omega
    have hnotPast : ∀ i, i < s + 1 → M.f i i ≠ z := by
      intro i hi
      exact margin_guard_hole_not_past M hdip hmargin i (by omega)
    exact (dip_hole_next_hosted_iff_no_consecutive_dip
      M hU hzPos hdiagHole hnotPast).1
      (by simpa [z] using hZ s hdip hmargin)
  · intro hNoConsec s hdip hmargin
    let z := M.f (s + 1) (s + 1) - 1
    have hzPos : 0 < z := by
      dsimp [z]
      have hgt := M.diagonal_gt (s + 1)
      omega
    have hdiagHole : M.f (s + 1) (s + 1) = z + 1 := by
      dsimp [z]
      have hgt := M.diagonal_gt (s + 1)
      omega
    have hnotPast : ∀ i, i < s + 1 → M.f i i ≠ z := by
      intro i hi
      exact margin_guard_hole_not_past M hdip hmargin i (by omega)
    have hhost : C M.f (s + 2) (s + 2) z :=
      (dip_hole_next_hosted_iff_no_consecutive_dip
        M hU hzPos hdiagHole hnotPast).2
        (hNoConsec s hdip hmargin)
    simpa [z] using hhost

/-- The strengthened RM2 reduction in its minimal margin-event form. -/
theorem twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
    (M : RecurrenceModel) (hU : UnitDip M)
    (hNoConsec : MarginNoConsecutiveDips M) :
    TwoStepDiagonalRecordLaw M :=
  twoStepRecordLaw_of_unitDip_marginZRehost M hU
    ((marginZRehost_iff_marginNoConsecutiveDips M hU).2 hNoConsec)

/-- Actual-game specialization of the minimal margin-event reduction. -/
theorem game_twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
    (hU : UnitDip gameRecurrenceModel)
    (hNoConsec : MarginNoConsecutiveDips gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel :=
  twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
    gameRecurrenceModel hU hNoConsec

#print axioms marginZRehost_iff_marginNoConsecutiveDips
#print axioms twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
#print axioms game_twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips

end ChompLean
