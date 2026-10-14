import R60R59ExactResidual

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
R60: retain the strong-induction information at the first RM2 failure.

The older event-E equivalence keeps only the numerical margin.  Choosing
the least failure of `RMax(k) < d(k+2)` gives more: that inequality already
holds at every earlier index.  This prefix law is genuine additional
structure on the counterexample while remaining exactly equivalent to
failure of RM2 under `UnitDip`.
-/

def RMaxTwoStepPrefix (M : RecurrenceModel) (s : Nat) : Prop :=
  forall j, j < s -> RMax M j < M.f (j + 2) (j + 2)

def FirstRMaxMarginEventE (s : Nat) : Prop :=
  MarginEventECounterexample s /\
  RMaxTwoStepPrefix gameRecurrenceModel s

private theorem exists_minimal_nat
    {P : Nat -> Prop} (hex : exists n, P n) :
    exists n, P n /\ forall m, m < n -> Not (P m) := by
  classical
  rcases hex with ⟨n, hn⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hearlier : exists m, m < n /\ P m
      · rcases hearlier with ⟨m, hmn, hm⟩
        exact ih m hmn hm
      · exact ⟨n, hn, by
          intro m hmn hm
          exact hearlier ⟨m, hmn, hm⟩⟩

theorem twoStepDiagonalRecordLaw_iff_rmax_twoStep
    (M : RecurrenceModel) :
    TwoStepDiagonalRecordLaw M <->
      forall k, RMax M k < M.f (k + 2) (k + 2) := by
  constructor
  · intro hrecord k
    rcases rmax_witness M k with ⟨i, hik, hmax⟩
    have hi := hrecord (i := i) (a := k + 2) (by omega)
    rw [hmax]
    exact hi
  · intro hrmax i a hia
    obtain ⟨k, hk⟩ : exists k, a = k + 2 :=
      ⟨a - 2, by omega⟩
    subst a
    exact Nat.lt_of_le_of_lt
      (rmax_ge M k i (by omega)) (hrmax k)

/-- At the least failed running-maximum comparison, all non-event
trichotomy arms close arithmetically.  The survivor is exactly a numerical
margin event E, and the earlier running-maximum comparisons are retained. -/
theorem first_rmax_failure_is_margin_event
    (M : RecurrenceModel) (hU : UnitDip M)
    {k : Nat}
    (hfail : Not (RMax M k < M.f (k + 2) (k + 2)))
    (hprior : RMaxTwoStepPrefix M k) :
    M.f (k + 1) (k + 1) < M.f k k /\
    (k = 0 \/
      exists j, k = j + 1 /\
        RMax M j < M.f (k + 1) (k + 1) - 1) /\
    M.f (k + 2) (k + 2) < M.f (k + 1) (k + 1) := by
  have hle : M.f (k + 2) (k + 2) <= RMax M k := by omega
  have hstrict : M.f (k + 2) (k + 2) < RMax M k := by
    apply Nat.lt_of_le_of_ne hle
    intro heq
    rcases rmax_witness M k with ⟨i, hik, hmax⟩
    have hdiagEq : M.f (k + 2) (k + 2) = M.f i i :=
      heq.trans hmax
    have hidx := diagonal_injective M hdiagEq
    omega
  have hcases :
      RMax M k = M.f k k \/
      exists j, k = j + 1 /\ RMax M k = RMax M j := by
    cases k with
    | zero => exact Or.inl rfl
    | succ j =>
        have hstep :
            RMax M (j + 1) =
              max (RMax M j) (M.f (j + 1) (j + 1)) := rfl
        by_cases h : RMax M j <= M.f (j + 1) (j + 1)
        · left
          omega
        · right
          exact ⟨j, rfl, by omega⟩
  have hdesc :
      M.f (k + 2) (k + 2) < M.f (k + 1) (k + 1) := by
    rcases Nat.lt_trichotomy
        (M.f (k + 1) (k + 1)) (M.f (k + 2) (k + 2)) with
      hasc | heq | hdesc
    · rcases hcases with hrecord | ⟨j, hkj, hold⟩
      · have hdip : M.f (k + 1) (k + 1) < M.f k k := by
          rw [← hrecord]
          omega
        have hu := hU k hdip
        omega
      · have hpast := hprior j (by omega)
        have hidx : j + 2 = k + 1 := by omega
        rw [hidx] at hpast
        omega
    · have hidx := diagonal_injective M heq
      omega
    · exact hdesc
  have hu2 :
      M.f (k + 2) (k + 2) + 1 = M.f (k + 1) (k + 1) :=
    hU (k + 1) hdesc
  have hrecord : RMax M k = M.f k k := by
    rcases hcases with hrecord | ⟨j, hkj, hold⟩
    · exact hrecord
    · have hpast := hprior j (by omega)
      have hidx : j + 2 = k + 1 := by omega
      rw [hidx] at hpast
      omega
  have hdiagNe : M.f (k + 1) (k + 1) ≠ M.f k k := by
    intro heq
    have hidx := diagonal_injective M heq
    omega
  have hdip : M.f (k + 1) (k + 1) < M.f k k := by
    rw [← hrecord]
    omega
  have hu1 := hU k hdip
  have hmargin :
      k = 0 \/
      exists j, k = j + 1 /\
        RMax M j < M.f (k + 1) (k + 1) - 1 := by
    cases k with
    | zero => exact Or.inl rfl
    | succ j =>
        right
        refine ⟨j, rfl, ?_⟩
        have hpast := hprior j (by omega)
        have hidx : j + 2 = j + 1 + 1 := by omega
        rw [hidx] at hpast
        have hne : RMax M j ≠ M.f (j + 1 + 2) (j + 1 + 2) := by
          intro heq
          rcases rmax_witness M j with ⟨i, hij, hmax⟩
          have hdiagEq : M.f i i = M.f (j + 1 + 2) (j + 1 + 2) :=
            hmax.symm.trans heq
          have hownerEq := diagonal_injective M hdiagEq
          omega
        have hu2' :
            M.f (j + 1 + 2) (j + 1 + 2) + 1 =
              M.f (j + 1 + 1) (j + 1 + 1) := by
          simpa [Nat.add_assoc] using hu2
        have hpred :
            M.f (j + 1 + 1) (j + 1 + 1) - 1 =
              M.f (j + 1 + 2) (j + 1 + 2) := by
          omega
        rw [hpred]
        have hle :
            RMax M j <= M.f (j + 1 + 2) (j + 1 + 2) := by
          omega
        exact Nat.lt_of_le_of_ne hle hne
  exact ⟨hdip, hmargin, hdesc⟩

theorem gameF_unitDip_not_RM2_iff_first_rmax_eventE
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      exists s, FirstRMaxMarginEventE s := by
  classical
  constructor
  · intro hnot
    have hex : exists k,
        Not (RMax gameRecurrenceModel k <
          gameF (k + 2) (k + 2)) := by
      apply Classical.byContradiction
      intro hnone
      apply hnot
      apply (twoStepDiagonalRecordLaw_iff_rmax_twoStep
        gameRecurrenceModel).2
      intro k
      apply Classical.byContradiction
      intro hk
      exact hnone ⟨k, hk⟩
    rcases exists_minimal_nat hex with ⟨k, hkFail, hkMinimal⟩
    have hkPrior : RMaxTwoStepPrefix gameRecurrenceModel k := by
      intro j hj
      apply Classical.byContradiction
      intro hjFail
      exact (hkMinimal j hj) hjFail
    have hgeom := first_rmax_failure_is_margin_event
      gameRecurrenceModel hU hkFail hkPrior
    exact ⟨k, hgeom, hkPrior⟩
  · rintro ⟨s, hEvent, _hprior⟩
    exact (gameF_unitDip_not_RM2_iff_exists_eventE hU).2
      ⟨s, hEvent⟩

#print axioms twoStepDiagonalRecordLaw_iff_rmax_twoStep
#print axioms first_rmax_failure_is_margin_event
#print axioms gameF_unitDip_not_RM2_iff_first_rmax_eventE

end ChompLean
