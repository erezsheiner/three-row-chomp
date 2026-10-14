import R23FutureOwnerRM2Escape

set_option autoImplicit false

namespace ChompLean

/-!
DipZRehostRM2Reduction — Lean form of the §10.2 sharpened reduction
(`3RowAss/RM2-CHARGE-LIFT-ATTACK-2026-07-11.md`):

  UNIT-DIP  ∧  Z-REHOST  ⟹  TwoStepDiagonalRecordLaw  (RM2Law, pointwise form)

with diagonal injectivity supplied by the model (`diagonal_injective`).

`UnitDip`: every dip drops by exactly one (`d(a+1) < d(a) ⟹ d(a+1)+1 = d(a)`).

`ZRehost`: after a dip at row `s+1` whose hole `z = d(s+1)−1` is not an earlier
diagonal value, `z` is interior-hosted on row `s+2`. In the first-violation
argument below, the margin-≥2 branch supplies this no-earlier-diagonal
guard using the preceding record control. The margin-1 branch is instead
excluded by diagonal injectivity. This is not an unrestricted equivalence
between the guard and a numerical margin condition at every dip.

NO-CONSEC-DIPS is not a hypothesis anywhere: the consecutive-dip endpoint of
the first-violation analysis is killed by `ZRehost` + fixed-row injectivity
(the hole, being covered on the next row, cannot be that row's fresh
diagonal emission).

Receipts: UnitDip 2030/2030 dips and ZRehost-sites 0 failures at N=136559
(`cache/dv_N152000.csv`); hole transport `V2(t−1)=z → V1(t)=z` 255/255 at
N=40000; landing at row t+1 in {V3, depth-5} 24/24 at F4000.
-/

/-- UNIT-DIP: every dip of the diagonal drops by exactly one. -/
def UnitDip (M : RecurrenceModel) : Prop :=
  ∀ a, M.f (a+1) (a+1) < M.f a a → M.f (a+1) (a+1) + 1 = M.f a a

/-- Z-REHOST: after a dip at row `s+1` whose hole `d(s+1)−1` is not an
earlier diagonal value, the hole is interior-hosted on row `s+2`. -/
def ZRehost (M : RecurrenceModel) : Prop :=
  ∀ s, M.f (s+1) (s+1) < M.f s s →
    (∀ j, j ≤ s → M.f j j ≠ M.f (s+1) (s+1) - 1) →
    C M.f (s+2) (s+2) (M.f (s+1) (s+1) - 1)

/-- Running maximum of the diagonal sequence. -/
def RMax (M : RecurrenceModel) : Nat → Nat
  | 0 => M.f 0 0
  | s+1 => max (RMax M s) (M.f (s+1) (s+1))

theorem rmax_ge (M : RecurrenceModel) :
    ∀ s i, i ≤ s → M.f i i ≤ RMax M s := by
  intro s
  induction s with
  | zero =>
      intro i hi
      have h0 : i = 0 := Nat.le_zero.mp hi
      subst h0
      exact Nat.le_refl _
  | succ s ih =>
      intro i hi
      have hstep : RMax M (s+1) = max (RMax M s) (M.f (s+1) (s+1)) := rfl
      by_cases h : i ≤ s
      · have := ih i h
        omega
      · have hi1 : i = s + 1 := by omega
        subst hi1
        omega

theorem rmax_witness (M : RecurrenceModel) :
    ∀ s, ∃ j, j ≤ s ∧ RMax M s = M.f j j := by
  intro s
  induction s with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ s ih =>
      rcases ih with ⟨j, hj, hEq⟩
      have hstep : RMax M (s+1) = max (RMax M s) (M.f (s+1) (s+1)) := rfl
      by_cases h : M.f (s+1) (s+1) ≤ RMax M s
      · exact ⟨j, by omega, by omega⟩
      · exact ⟨s+1, Nat.le_refl _, by omega⟩

/-- Core first-violation induction: under `UnitDip` and `ZRehost`, the
diagonal strictly dominates its running maximum two rows back. -/
theorem rmax_lt_of_unitDip_zrehost (M : RecurrenceModel)
    (hU : UnitDip M) (hZ : ZRehost M) :
    ∀ k, RMax M k < M.f (k+2) (k+2) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    refine Nat.not_le.mp ?_
    intro hle
    rcases rmax_witness M k with ⟨m, hmk, hmax⟩
    -- injectivity upgrades to strict: d(k+2) < RMax k
    have hstrict : M.f (k+2) (k+2) < RMax M k := by
      rcases Nat.lt_or_ge (M.f (k+2) (k+2)) (RMax M k) with h | h
      · exact h
      · exfalso
        have hEq : M.f (k+2) (k+2) = M.f m m := by omega
        have := diagonal_injective M hEq
        omega
    -- record-position dichotomy for RMax k
    have hcases : RMax M k = M.f k k ∨ ∃ j, k = j + 1 ∧ RMax M k = RMax M j := by
      cases k with
      | zero => exact Or.inl rfl
      | succ j =>
          have hstep : RMax M (j+1) = max (RMax M j) (M.f (j+1) (j+1)) := rfl
          by_cases h : RMax M j ≤ M.f (j+1) (j+1)
          · left; omega
          · right; exact ⟨j, rfl, by omega⟩
    -- trichotomy at the violation row
    rcases Nat.lt_trichotomy (M.f (k+1) (k+1)) (M.f (k+2) (k+2)) with hasc | heq | hdesc
    · -- ASCENDING violation
      rcases hcases with hrec | ⟨j, hkj, hold⟩
      · -- record at k: d(k+1) < d(k+2) < d(k), so dip at k+1 into an empty unit interval
        have hdip : M.f (k+1) (k+1) < M.f k k := by omega
        have := hU k hdip
        omega
      · -- old record: RMax j = RMax k > d(k+2) > d(k+1) contradicts induction at j
        have hIH := ih j (by omega)
        have hidx : j + 2 = k + 1 := by omega
        rw [hidx] at hIH
        omega
    · -- equal diagonals: impossible by injectivity
      have := diagonal_injective M heq
      omega
    · -- DESCENDING violation: dip at k+2
      have hu2 : M.f (k+2) (k+2) + 1 = M.f (k+1) (k+1) := hU (k+1) hdesc
      rcases hcases with hrec | ⟨j, hkj, hold⟩
      · -- record at k: forced consecutive dip, killed by ZRehost + row injectivity
        have hne1 : M.f (k+1) (k+1) ≠ M.f k k := by
          intro hEq
          have := diagonal_injective M hEq
          omega
        have hdip1 : M.f (k+1) (k+1) < M.f k k := by omega
        have hhole : M.f (k+1) (k+1) - 1 = M.f (k+2) (k+2) := by omega
        have hnotpast : ∀ j2, j2 ≤ k → M.f j2 j2 ≠ M.f (k+1) (k+1) - 1 := by
          intro j2 hj2 hEq
          rw [hhole] at hEq
          have := diagonal_injective M hEq
          omega
        have hC : ∃ b, b < k + 2 ∧ M.f (k+2) b = M.f (k+1) (k+1) - 1 :=
          hZ k hdip1 hnotpast
        rcases hC with ⟨b, hb, hfb⟩
        rw [hhole] at hfb
        have := M.fixed_q_injective (Nat.le_of_lt hb) (Nat.le_refl (k+2)) hfb
        omega
      · -- old record: induction at j squeezes the unit dip
        have hIH := ih j (by omega)
        have hidx : j + 2 = k + 1 := by omega
        rw [hidx] at hIH
        omega

/-- §10.2 sharpened reduction (abstract model form):
`UNIT-DIP ∧ Z-REHOST ⟹ RM2Law` (pointwise `TwoStepDiagonalRecordLaw`).
NO-CONSEC-DIPS is not assumed. -/
theorem twoStepRecordLaw_of_unitDip_zrehost (M : RecurrenceModel)
    (hU : UnitDip M) (hZ : ZRehost M) :
    TwoStepDiagonalRecordLaw M := by
  intro i a hia
  rcases (⟨a - 2, by omega⟩ : ∃ k, a = k + 2) with ⟨k, hk⟩
  subst hk
  exact Nat.lt_of_le_of_lt (rmax_ge M k i (by omega))
    (rmax_lt_of_unitDip_zrehost M hU hZ k)

/-- The reduction instantiated at the actual 3-row Chomp encoding. -/
theorem game_twoStepRecordLaw_of_unitDip_zrehost
    (hU : UnitDip gameRecurrenceModel) (hZ : ZRehost gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel :=
  twoStepRecordLaw_of_unitDip_zrehost gameRecurrenceModel hU hZ

#print axioms twoStepRecordLaw_of_unitDip_zrehost
#print axioms game_twoStepRecordLaw_of_unitDip_zrehost

end ChompLean
