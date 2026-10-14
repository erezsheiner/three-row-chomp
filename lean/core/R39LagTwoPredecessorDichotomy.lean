import R36MarginEventETwoRideCertificate
import R33UnitDipFirstGapTrichotomy
import R38DiagonalFirstGapChronologyAudit

set_option autoImplicit false

namespace ChompLean

/-!
Lag-two slice of the delayed-diagonal-predecessor obstruction.

If `d(a)=x+1` and `d(a+2)=x`, then either the middle diagonal falls below
`x`, which is already a non-unit dip at `a`, or `x` lies below the middle
diagonal.  In the latter case exact MEX forces `x` to be hosted on both rows
`a` and `a+1`; actual no-repeat makes the host columns distinct, and row
`a+2` emits `x`.  Thus the delayed predecessor is either a UnitDip
obstruction or a two-ride-then-emit obstruction.
-/

/-- Exact lag-two dichotomy, using neither RM2 nor UnitDip. -/
theorem gameF_lag_two_predecessor_is_nonunit_dip_or_two_ride
    {a x : Nat}
    (hPrev : gameF a a = x + 1)
    (hOwner : gameF (a + 2) (a + 2) = x) :
    DipFirstGap gameRecurrenceModel a < gameF a a ∨
      ∃ b₀ b₁,
        b₀ < a ∧ b₁ < a + 1 ∧ b₀ ≠ b₁ ∧
        gameF a b₀ = x ∧ gameF (a + 1) b₁ = x ∧
        gameF (a + 2) (a + 2) = x ∧
        ¬ B gameF (a + 2) (a + 2) x := by
  have hxPos : 0 < x := by
    have hgt := gameRecurrenceModel.diagonal_gt (a + 2)
    change a + 2 < gameF (a + 2) (a + 2) at hgt
    rw [hOwner] at hgt
    omega
  have hxBelowPrev : x < gameF a a := by omega
  have hBPrev : B gameF a a x :=
    gameRecurrenceModel.mex_no_skip (Nat.le_refl a)
      (gameRecurrenceModel.diagonal_gt a) hxPos hxBelowPrev
  have hCPrev : C gameF a a x := by
    rcases hBPrev with hR | hC
    · rcases hR with ⟨i, hia, hvalue⟩
      have hmin : min i a = i := Nat.min_eq_left (Nat.le_of_lt hia)
      rw [hmin] at hvalue
      have hidx := diagonal_injective gameRecurrenceModel
        (hvalue.trans hOwner.symm)
      omega
    · exact hC
  rcases hCPrev with ⟨b₀, hb₀, hhost₀⟩
  by_cases hmidLow : gameF (a + 1) (a + 1) < x
  · left
    change gameF (a + 1) (a + 1) + 1 < gameF a a
    rw [hPrev]
    omega
  · have hmidNe : gameF (a + 1) (a + 1) ≠ x := by
      intro hEq
      have hdiagEq :
          gameF (a + 1) (a + 1) = gameF (a + 2) (a + 2) := by
        rw [hEq, hOwner]
      have hidx := diagonal_injective gameRecurrenceModel hdiagEq
      omega
    have hxBelowMid : x < gameF (a + 1) (a + 1) := by omega
    have hBMid : B gameF (a + 1) (a + 1) x :=
      gameRecurrenceModel.mex_no_skip (Nat.le_refl (a + 1))
        (gameRecurrenceModel.diagonal_gt (a + 1)) hxPos hxBelowMid
    have hCMid : C gameF (a + 1) (a + 1) x := by
      rcases hBMid with hR | hC
      · rcases hR with ⟨i, hi, hvalue⟩
        have hmin : min i (a + 1) = i :=
          Nat.min_eq_left (Nat.le_of_lt hi)
        rw [hmin] at hvalue
        have hidx := diagonal_injective gameRecurrenceModel
          (hvalue.trans hOwner.symm)
        omega
      · exact hC
    rcases hCMid with ⟨b₁, hb₁, hhost₁⟩
    have haBelowX : a + 1 < x := by
      have hgt := gameRecurrenceModel.diagonal_gt (a + 2)
      change a + 2 < gameF (a + 2) (a + 2) at hgt
      rw [hOwner] at hgt
      omega
    have hbNe : b₀ ≠ b₁ := by
      intro hEq
      subst b₁
      exact encoding_same_lower_no_repeat game_encodes
        hb₀ (by omega) haBelowX hhost₀ hhost₁
    have hAbsent : ¬ B gameF (a + 2) (a + 2) x := by
      have hmex := recurrence_diagonal_exact_mex
        gameRecurrenceModel (a + 2)
      change IsMex (B gameF (a + 2) (a + 2))
        (gameF (a + 2) (a + 2)) at hmex
      rw [hOwner] at hmex
      exact hmex.2.1
    exact Or.inr ⟨b₀, b₁, hb₀, hb₁, hbNe,
      hhost₀, hhost₁, hOwner, hAbsent⟩

/-- Under UnitDip, the non-unit branch of the lag-two dichotomy is
impossible, so every lag-two predecessor would be a two-ride-then-emit
episode. -/
theorem gameF_lag_two_predecessor_forces_two_ride_of_unitDip
    (hU : UnitDip gameRecurrenceModel) {a x : Nat}
    (hPrev : gameF a a = x + 1)
    (hOwner : gameF (a + 2) (a + 2) = x) :
    ∃ b₀ b₁,
      b₀ < a ∧ b₁ < a + 1 ∧ b₀ ≠ b₁ ∧
      gameF a b₀ = x ∧ gameF (a + 1) b₁ = x ∧
      gameF (a + 2) (a + 2) = x := by
  rcases gameF_lag_two_predecessor_is_nonunit_dip_or_two_ride
      hPrev hOwner with hgap | hride
  · have hdip : gameF (a + 1) (a + 1) < gameF a a := by
      change gameF (a + 1) (a + 1) + 1 < gameF a a at hgap
      omega
    have hunit := hU a hdip
    have hunit' :
        gameF (a + 1) (a + 1) + 1 = gameF a a := by
      simpa using hunit
    have hgap' :
        gameF (a + 1) (a + 1) + 1 < gameF a a := by
      simpa [DipFirstGap] using hgap
    rw [← hunit'] at hgap'
    exact False.elim (Nat.lt_irrefl _ hgap')
  · rcases hride with
      ⟨b₀, b₁, hb₀, hb₁, hbNe, hhost₀, hhost₁, hEmit, _⟩
    exact ⟨b₀, b₁, hb₀, hb₁, hbNe, hhost₀, hhost₁, hEmit⟩

/-- Consequently the two scheduler laws already isolated for RM2 exclude
every lag-two reverse-adjacent diagonal pair. -/
theorem gameF_no_lag_two_diagonal_predecessor_of_unitDip_noTwoRide
    (hU : UnitDip gameRecurrenceModel)
    (hNoRide : NoTwoRideThenDiagonalEmit gameF) :
    ∀ a, gameF a a ≠ gameF (a + 2) (a + 2) + 1 := by
  intro a hEq
  let x := gameF (a + 2) (a + 2)
  have hPrev : gameF a a = x + 1 := by simpa [x] using hEq
  have hOwner : gameF (a + 2) (a + 2) = x := rfl
  rcases gameF_lag_two_predecessor_forces_two_ride_of_unitDip
      hU hPrev hOwner with
    ⟨b₀, b₁, hb₀, hb₁, hbNe, hhost₀, hhost₁, hEmit⟩
  exact hNoRide hb₀ hb₁ hbNe hhost₀ hhost₁ hEmit

/-- In fact the whole delayed-predecessor law follows from UnitDip alone.
Starting at `x+1`, reaching the fresh value `x` later would have a first row
at or below `x`.  The unit dip into that row must come from `x+1`, repeating
the original diagonal and contradicting diagonal injectivity. -/
theorem noDelayedDiagonalPredecessor_of_unitDip
    (M : RecurrenceModel) (hU : UnitDip M) :
    NoDelayedDiagonalPredecessor M := by
  intro a t hat hEq
  let x := M.f t t
  have hPrev : M.f a a = x + 1 := by
    simpa [x] using hEq
  have hAbove :
      ∀ n, a + 1 + n ≤ t → x < M.f (a + 1 + n) (a + 1 + n) := by
    intro n
    induction n with
    | zero =>
        intro hle
        have hklt : a + 1 < t := by omega
        apply Nat.lt_of_not_ge
        intro hlow
        have hlow' : M.f (a + 1) (a + 1) ≤ x := by
          simpa using hlow
        have hdip : M.f (a + 1) (a + 1) < M.f a a := by
          rw [hPrev]
          omega
        have hunitRaw := hU a hdip
        have hunit : M.f (a + 1) (a + 1) + 1 = M.f a a := by
          simpa using hunitRaw
        have hkEq : M.f (a + 1) (a + 1) = x := by
          rw [hPrev] at hunit
          omega
        have hdiagEq : M.f (a + 1) (a + 1) = M.f t t := by
          simpa [x] using hkEq
        have hidx := diagonal_injective M hdiagEq
        omega
    | succ n ih =>
        intro hle
        have hprev : x < M.f (a + 1 + n) (a + 1 + n) :=
          ih (by omega)
        apply Nat.lt_of_not_ge
        intro hnextLow
        have hnextLow' :
            M.f ((a + 1 + n) + 1) ((a + 1 + n) + 1) ≤ x := by
          simpa [Nat.add_assoc] using hnextLow
        have hdip :
            M.f ((a + 1 + n) + 1) ((a + 1 + n) + 1) <
              M.f (a + 1 + n) (a + 1 + n) := by
          omega
        have hunitRaw := hU (a + 1 + n) hdip
        have hunit :
            M.f ((a + 1 + n) + 1) ((a + 1 + n) + 1) + 1 =
              M.f (a + 1 + n) (a + 1 + n) := by
          simpa [Nat.add_assoc] using hunitRaw
        have hprevEq : M.f (a + 1 + n) (a + 1 + n) = x + 1 := by
          omega
        have hdiagEq : M.f (a + 1 + n) (a + 1 + n) = M.f a a :=
          hprevEq.trans hPrev.symm
        have hidx := diagonal_injective M hdiagEq
        omega
  let n := t - (a + 1)
  have hsum : a + 1 + n = t := by
    dsimp [n]
    omega
  have hfinal := hAbove n (by omega)
  rw [hsum] at hfinal
  dsimp [x] at hfinal
  omega

/-- Exact two-part replacement for the three-way first-gap formulation of
UnitDip.  The past-diagonal branch is absorbed into the global delayed-
predecessor chronology law; the other two branches remain explicit. -/
theorem unitDip_iff_noDelayed_and_noFutureOrLate
    (M : RecurrenceModel) :
    UnitDip M ↔
      NoDelayedDiagonalPredecessor M ∧
        ∀ s,
          ¬ DipFirstGapFutureDiagonalLoss M s ∧
          ¬ DipFirstGapLateBlockerLoss M s := by
  constructor
  · intro hU
    have hAll := (unitDip_iff_no_first_gap_obstructions M).1 hU
    refine ⟨noDelayedDiagonalPredecessor_of_unitDip M hU, ?_⟩
    intro s
    exact ⟨(hAll s).2.1, (hAll s).2.2⟩
  · rintro ⟨hNoDelay, hNoRest⟩
    exact
      (unitDip_iff_no_future_or_late_first_gap_of_noDelayedPredecessor
        M hNoDelay).2 hNoRest

/-- Updated RM2 interface using the exact two-part UnitDip decomposition. -/
theorem twoStepRecordLaw_of_noDelayed_noFuture_noLate_marginEvent
    (M : RecurrenceModel)
    (hNoDelay : NoDelayedDiagonalPredecessor M)
    (hNoRest : ∀ s,
      ¬ DipFirstGapFutureDiagonalLoss M s ∧
      ¬ DipFirstGapLateBlockerLoss M s)
    (hMarginEvent : MarginNoConsecutiveDips M) :
    TwoStepDiagonalRecordLaw M := by
  have hU : UnitDip M :=
    (unitDip_iff_noDelayed_and_noFutureOrLate M).2
      ⟨hNoDelay, hNoRest⟩
  intro i a hia
  exact twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
    M hU hMarginEvent hia

#print axioms gameF_lag_two_predecessor_is_nonunit_dip_or_two_ride
#print axioms gameF_no_lag_two_diagonal_predecessor_of_unitDip_noTwoRide
#print axioms noDelayedDiagonalPredecessor_of_unitDip
#print axioms unitDip_iff_noDelayed_and_noFutureOrLate
#print axioms twoStepRecordLaw_of_noDelayed_noFuture_noLate_marginEvent

end ChompLean
