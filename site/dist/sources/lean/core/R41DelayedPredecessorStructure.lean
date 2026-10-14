import R39LagTwoPredecessorDichotomy
import R40FutureDiagonalPrehostCharge

set_option autoImplicit false

namespace ChompLean

/-!
General structural form of a delayed reverse-adjacent diagonal pair.

If `d(a)=d(t)+1` with `a+2<=t`, exact MEX at row `a` forces the future
diagonal value `d(t)` into the strict prefix of row `a`.  At its owner row
`t` the same value is absent from the diagonal source.  Hence every delayed
predecessor is a `FutureDiagonalPrehostLoss`, and the owner-band theorem
forces at least four units of diagonal slack at row `a`.
-/

/-- Every delayed diagonal predecessor is a future-diagonal prehost loss. -/
theorem delayedDiagonalPredecessor_is_futurePrehostLoss
    (M : RecurrenceModel) {a t : Nat}
    (hdelay : a + 2 ≤ t)
    (hPred : M.f a a = M.f t t + 1) :
    FutureDiagonalPrehostLoss M a t (M.f t t) := by
  let x := M.f t t
  have hxPos : 0 < x := by
    dsimp [x]
    have hgt := M.diagonal_gt t
    omega
  have hxBelow : x < M.f a a := by
    rw [hPred]
    dsimp [x]
    omega
  have hB : B M.f a a x :=
    (recurrence_diagonal_exact_mex M a).2.2 x hxPos hxBelow
  have hC : C M.f a a x := by
    rcases hB with hR | hC
    · rcases hR with ⟨i, hia, hvalue⟩
      have hmin : min i a = i := Nat.min_eq_left (Nat.le_of_lt hia)
      rw [hmin] at hvalue
      have hdiagEq : M.f i i = M.f t t := by
        simpa [x] using hvalue
      have hidx := diagonal_injective M hdiagEq
      omega
    · exact hC
  have hAbsent : ¬ B M.f t t x := by
    dsimp [x]
    exact (recurrence_diagonal_exact_mex M t).2.1
  exact ⟨by omega, rfl, hC, hAbsent⟩

/-- Unconditional slack cost of a delayed reverse-adjacent pair. -/
theorem delayedDiagonalPredecessor_forces_slack_four
    (M : RecurrenceModel) {a t : Nat}
    (hdelay : a + 2 ≤ t)
    (hPred : M.f a a = M.f t t + 1) :
    a + 4 ≤ M.f a a := by
  have hloss := delayedDiagonalPredecessor_is_futurePrehostLoss
    M hdelay hPred
  exact delayed_futureDiagonalPrehost_forces_slack_four
    M hloss hdelay

/-- A row of diagonal slack at most three cannot be the old endpoint of a
delayed predecessor pair.  This eliminates a genuine class without RM2 or
UnitDip. -/
theorem noDelayedDiagonalPredecessor_from_low_slack_row
    (M : RecurrenceModel) {a : Nat}
    (hslack : M.f a a ≤ a + 3) :
    ∀ {t}, a + 2 ≤ t → M.f a a ≠ M.f t t + 1 := by
  intro t hdelay hPred
  have hfour := delayedDiagonalPredecessor_forces_slack_four
    M hdelay hPred
  omega

/-- Equivalent support restriction: any failure of
`NoDelayedDiagonalPredecessor` must start at a row of slack at least four. -/
theorem delayedPredecessor_failure_has_slack_four
    (M : RecurrenceModel)
    (hFail : ¬ NoDelayedDiagonalPredecessor M) :
    ∃ a t,
      a + 2 ≤ t ∧
      M.f a a = M.f t t + 1 ∧
      a + 4 ≤ M.f a a := by
  classical
  apply Classical.byContradiction
  intro hNoWitness
  apply hFail
  intro a t hdelay hPred
  apply hNoWitness
  exact ⟨a, t, hdelay, hPred,
    delayedDiagonalPredecessor_forces_slack_four M hdelay hPred⟩

#print axioms delayedDiagonalPredecessor_is_futurePrehostLoss
#print axioms delayedDiagonalPredecessor_forces_slack_four
#print axioms noDelayedDiagonalPredecessor_from_low_slack_row
#print axioms delayedPredecessor_failure_has_slack_four

end ChompLean
