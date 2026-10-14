import DipZRehostRM2Reduction

set_option autoImplicit false

namespace ChompLean

/-!
`ZRehost` is the service formulation of the post-dip obstruction.  This file
isolates the strictly smaller-looking assignment statement saying that the
hole immediately below a dip diagonal is not the very next diagonal.

Under `UnitDip`, the following three formulations are equivalent:

* the guarded service statement `ZRehost`;
* the unguarded one-value assignment statement `DipHoleNotNextDiagonal`;
* absence of consecutive dips.

Thus `ZRehost` is useful geometrically, but it does not remove the
post-dip-assignment wall once `UnitDip` is assumed.
-/

/-- The value immediately below a dip diagonal is not emitted by the very
next diagonal.  Unlike `ZRehost`, this statement has no past-diagonal guard
and makes no assertion about where the value is hosted. -/
def DipHoleNotNextDiagonal (M : RecurrenceModel) : Prop :=
  ∀ s, M.f (s + 1) (s + 1) < M.f s s →
    M.f (s + 2) (s + 2) ≠ M.f (s + 1) (s + 1) - 1

/-- There are no dips on two consecutive row transitions. -/
def NoConsecutiveDips (M : RecurrenceModel) : Prop :=
  ∀ s, M.f (s + 1) (s + 1) < M.f s s →
    ¬ M.f (s + 2) (s + 2) < M.f (s + 1) (s + 1)

/-- Under unit-depth dips, excluding the next emission of the dip hole is
exactly the same as excluding consecutive dips. -/
theorem dipHoleNotNextDiagonal_iff_noConsecutiveDips
    (M : RecurrenceModel) (hU : UnitDip M) :
    DipHoleNotNextDiagonal M ↔ NoConsecutiveDips M := by
  constructor
  · intro hNoEmit s hdip hnextDip
    have hunit := hU (s + 1) hnextDip
    have hunit' :
        M.f (s + 2) (s + 2) + 1 = M.f (s + 1) (s + 1) := by
      simpa [Nat.add_assoc] using hunit
    have hEq :
        M.f (s + 2) (s + 2) = M.f (s + 1) (s + 1) - 1 := by
      have hpos := M.diagonal_gt (s + 2)
      omega
    exact hNoEmit s hdip hEq
  · intro hNoConsec s hdip hEq
    apply hNoConsec s hdip
    have hpos := M.diagonal_gt (s + 1)
    omega

/-- `ZRehost` excludes the next emission.  If the past-diagonal guard needed
by `ZRehost` were to fail, diagonal injectivity against the assumed next
emission supplies the contradiction directly. -/
theorem dipHoleNotNextDiagonal_of_zRehost
    (M : RecurrenceModel) (hZ : ZRehost M) :
    DipHoleNotNextDiagonal M := by
  intro s hdip hEq
  have hnotPast :
      ∀ j, j ≤ s → M.f j j ≠ M.f (s + 1) (s + 1) - 1 := by
    intro j hjs hj
    have hdiagEq : M.f j j = M.f (s + 2) (s + 2) := hj.trans hEq.symm
    have hidx := diagonal_injective M hdiagEq
    omega
  rcases hZ s hdip hnotPast with ⟨b, hb, hfb⟩
  have hrowEq : M.f (s + 2) b = M.f (s + 2) (s + 2) :=
    hfb.trans hEq.symm
  have hidx := M.fixed_q_injective
    (Nat.le_of_lt hb) (Nat.le_refl (s + 2)) hrowEq
  omega

/-- Conversely, `UnitDip` and no next emission force the next diagonal above
the hole.  Diagonal MEX coverage then hosts the hole in the strict row prefix;
the `R` branch is excluded by the past-diagonal guard. -/
theorem zRehost_of_unitDip_dipHoleNotNextDiagonal
    (M : RecurrenceModel) (hU : UnitDip M)
    (hNoEmit : DipHoleNotNextDiagonal M) :
    ZRehost M := by
  intro s hdip hnotPast
  let z := M.f (s + 1) (s + 1) - 1
  have hzPos : 0 < z := by
    dsimp [z]
    have hgt := M.diagonal_gt (s + 1)
    omega
  have hnextFloor : M.f (s + 1) (s + 1) ≤ M.f (s + 2) (s + 2) := by
    apply Nat.le_of_not_gt
    intro hnextDip
    have hunit := hU (s + 1) hnextDip
    have hunit' :
        M.f (s + 2) (s + 2) + 1 = M.f (s + 1) (s + 1) := by
      simpa [Nat.add_assoc] using hunit
    have hEq : M.f (s + 2) (s + 2) = z := by
      dsimp [z]
      omega
    exact hNoEmit s hdip (by simpa [z] using hEq)
  have hzBelow : z < M.f (s + 2) (s + 2) := by
    dsimp [z]
    have hgt := M.diagonal_gt (s + 1)
    omega
  have hB : B M.f (s + 2) (s + 2) z :=
    M.mex_no_skip (Nat.le_refl (s + 2)) (M.diagonal_gt (s + 2))
      hzPos hzBelow
  rcases hB with hR | hC
  · rcases hR with ⟨a, ha, hfa⟩
    have hmin : min a (s + 2) = a := Nat.min_eq_left (Nat.le_of_lt ha)
    rw [hmin] at hfa
    by_cases has : a ≤ s
    · exact False.elim (hnotPast a has hfa)
    · have haeq : a = s + 1 := by omega
      subst a
      dsimp [z] at hfa
      have hgt := M.diagonal_gt (s + 1)
      omega
  · simpa [z] using hC

/-- Exact audit theorem: under `UnitDip`, the service and next-emission
formulations coincide. -/
theorem zRehost_iff_dipHoleNotNextDiagonal
    (M : RecurrenceModel) (hU : UnitDip M) :
    ZRehost M ↔ DipHoleNotNextDiagonal M := by
  constructor
  · exact dipHoleNotNextDiagonal_of_zRehost M
  · exact zRehost_of_unitDip_dipHoleNotNextDiagonal M hU

/-- The three post-dip formulations form one equivalence class once
`UnitDip` is available. -/
theorem zRehost_iff_noConsecutiveDips
    (M : RecurrenceModel) (hU : UnitDip M) :
    ZRehost M ↔ NoConsecutiveDips M := by
  rw [zRehost_iff_dipHoleNotNextDiagonal M hU]
  exact dipHoleNotNextDiagonal_iff_noConsecutiveDips M hU

/-- RM2 reduction with the minimal one-value assignment atom. -/
theorem twoStepRecordLaw_of_unitDip_dipHoleNotNextDiagonal
    (M : RecurrenceModel) (hU : UnitDip M)
    (hNoEmit : DipHoleNotNextDiagonal M) :
    TwoStepDiagonalRecordLaw M :=
  twoStepRecordLaw_of_unitDip_zrehost M hU
    (zRehost_of_unitDip_dipHoleNotNextDiagonal M hU hNoEmit)

/-- RM2 reduction in the familiar no-consecutive-dips form. -/
theorem twoStepRecordLaw_of_unitDip_noConsecutiveDips
    (M : RecurrenceModel) (hU : UnitDip M)
    (hNoConsec : NoConsecutiveDips M) :
    TwoStepDiagonalRecordLaw M :=
  twoStepRecordLaw_of_unitDip_dipHoleNotNextDiagonal M hU
    ((dipHoleNotNextDiagonal_iff_noConsecutiveDips M hU).2 hNoConsec)

/-! ## Owner and timing localization -/

/-- A positive hole immediately below a diagonal is either a row-start value
or has a diagonal owner strictly in the future.  Excluding past owners is the
only chronology input. -/
theorem dipHole_is_rowstart_or_future_diagonal
    (M : RecurrenceModel) {t z : Nat}
    (hzPos : 0 < z) (hdiag : M.f t t = z + 1)
    (hnotPast : ∀ j, j < t → M.f j j ≠ z) :
    (∃ r, r < z ∧ M.f z r = z) ∨
      ∃ a, t + 1 ≤ a ∧ a < z ∧ M.f a a = z := by
  rcases M.opening_cover hzPos with hD | hS
  · right
    rcases hD with ⟨a, haz, haOwner⟩
    have hta : t + 1 ≤ a := by
      by_cases hat : a < t
      · exact False.elim (hnotPast a hat haOwner)
      · by_cases hae : a = t
        · subst a
          rw [hdiag] at haOwner
          omega
        · omega
    exact ⟨a, hta, haz, haOwner⟩
  · exact Or.inl hS

/-- Any diagonal emission of the dip hole at least two rows later is already
an explicit pointwise failure of the two-step record law. -/
theorem delayed_dipHole_owner_forces_twoStepRecord_failure
    (M : RecurrenceModel) {t z a : Nat}
    (hdiag : M.f t t = z + 1)
    (hdelay : t + 2 ≤ a) (haOwner : M.f a a = z) :
    t + 2 ≤ a ∧ M.f a a < M.f t t := by
  constructor
  · exact hdelay
  · rw [haOwner, hdiag]
    omega

/-- Complete timing trichotomy for a guarded dip hole: blocker, immediate
next-diagonal capture (event E), or a delayed owner carrying an explicit RM2
counterexample. -/
theorem dipHole_owner_timing_trichotomy
    (M : RecurrenceModel) {t z : Nat}
    (hzPos : 0 < z) (hdiag : M.f t t = z + 1)
    (hnotPast : ∀ j, j < t → M.f j j ≠ z) :
    (∃ r, r < z ∧ M.f z r = z) ∨
      M.f (t + 1) (t + 1) = z ∨
      ∃ a, t + 2 ≤ a ∧ a < z ∧ M.f a a = z ∧
        M.f a a < M.f t t := by
  rcases dipHole_is_rowstart_or_future_diagonal
      M hzPos hdiag hnotPast with hS | hD
  · exact Or.inl hS
  · rcases hD with ⟨a, hta, haz, haOwner⟩
    by_cases haNext : a = t + 1
    · subst a
      exact Or.inr (Or.inl haOwner)
    · have hdelay : t + 2 ≤ a := by omega
      have hfailure := delayed_dipHole_owner_forces_twoStepRecord_failure
        M hdiag hdelay haOwner
      exact Or.inr (Or.inr
        ⟨a, hdelay, haz, haOwner, hfailure.2⟩)

#print axioms zRehost_iff_noConsecutiveDips
#print axioms twoStepRecordLaw_of_unitDip_dipHoleNotNextDiagonal
#print axioms dipHole_owner_timing_trichotomy

end ChompLean
