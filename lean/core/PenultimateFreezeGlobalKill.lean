import DensePrefixPenultimateFreezeKill
import DensePrefixAggregateGapOneClosure
import R66StageA
import R37UnitDipLateBlockerCharge

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
The penultimate-freeze closure is not specific to the dense `A_k` word.

For `v >= 5`, the clean-column proof from
`DensePrefixPenultimateFreezeKill` still works at column `v-2`.  Moreover,
the only possible failure of `PenultimateOwnerCovered v` is the immediately
preceding boundary opening

`gameF (v-1) (v-2) = v-1`.

Consequently a boundary opening at `v` propagates one step backward.  Strong
induction reaches `v=4`, where it conflicts with the diagonal owner
`gameF 2 2 = 4`.  Hence no boundary `V1` exists from row five onward.  This
removes the boundary arm of R37/R40's late-blocker split, but it does not
remove the remaining high-`V1`/R27 arm and says nothing directly about the
late-blocker freeze column of the first-gap value.
-/

/-- The clean penultimate candidate only needs `v>=5`; then `v-2>2`, so
the exact lag-two host at column `2` and lag-one host at column `0` both
miss the candidate column `v-2`. -/
theorem gameF_penultimate_candidate_clean_of_five
    {v : Nat} (hv : 5 <= v) :
    Not (ColHistPred gameF v (v - 2) v) := by
  rintro ⟨a, hca, hav, hvalue⟩
  have haCases : a = v - 2 ∨ a = v - 1 := by omega
  rcases haCases with ha | ha
  · subst a
    have hq : 2 <= v - 2 := by omega
    have hcol := gameF_lag_two_host_only_col2
      (q := v - 2) (c := v - 2) hq (Nat.le_refl _) (by
        simpa [show v - 2 + 2 = v by omega] using hvalue)
    omega
  · have hrow : a = (v - 2) + 1 := by omega
    have hcol := gameF_lag_one_host_only_col0
      (q := v - 2) (c := v - 2) (by omega) (by
        rw [hrow] at hvalue
        simpa [show v - 2 + 2 = v by omega] using hvalue)
    omega

/-- The one-column owner-coverage contradiction with its sharp small
threshold `v>=5`. -/
theorem gameF_no_penultimate_freeze_of_owner_coverage_of_five
    {v : Nat}
    (hv : 5 <= v)
    (hstart : gameF v (v - 1) = v)
    (howners : PenultimateOwnerCovered v) : False := by
  let c := v - 2
  have hcv : c <= v := by dsimp [c]; omega

  have hnotCarry : Not (c < v /\ gameF (v - 1) c < v) := by
    rintro ⟨hcvt, hprevLow⟩
    have hcprev : c <= v - 1 := by dsimp [c]; omega
    have hrow := gameF_low_cell_has_rowstart hcprev (by omega)
    let k := gameF (v - 1) c
    have hkpos : 0 < k := by dsimp [k]; omega
    have hkv : k < v := hprevLow
    rcases howners k hkpos hkv with
        ⟨a, _hac, hdiag⟩ | ⟨r, hrc, hrk, hstart'⟩
    · exact disjoint_D_S gameRecurrenceModel
        ⟨a, hdiag⟩ ⟨c, hrow.1, hrow.2⟩
    · have hcr : c = r :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hrow.1) (Nat.le_of_lt hrk)
          (hrow.2.trans hstart'.symm)
      dsimp [c] at hcr
      omega

  have hclean : Not (ColHistPred gameF v c v) := by
    dsimp [c]
    exact gameF_penultimate_candidate_clean_of_five hv

  have habsent : Not (B gameF v c v) := by
    intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, hav, hvalue⟩
      by_cases hac : a < c
      · have hmin : min a c = a := Nat.min_eq_left (Nat.le_of_lt hac)
        have hdiag : gameF a a = v := by simpa [hmin] using hvalue
        exact disjoint_D_S gameRecurrenceModel
          ⟨a, hdiag⟩ ⟨v - 1, by omega, hstart⟩
      · apply hclean
        have hca : c <= a := Nat.le_of_not_gt hac
        have hmin : min a c = c := Nat.min_eq_right hca
        exact ⟨a, hca, hav, by simpa [hmin] using hvalue⟩
    · rcases hC with ⟨b, hbc, hvalue⟩
      have hbr : b = v - 1 :=
        gameRecurrenceModel.fixed_q_injective
          (by dsimp [c] at hbc; omega) (by omega)
          (hvalue.trans hstart.symm)
      dsimp [c] at hbc
      omega

  have hlower : forall k, 0 < k -> k < v -> B gameF v c k := by
    dsimp [c]
    exact penultimateOwnerCovered_source_saturation (by omega) howners

  have hcandidate : gameF v c = v :=
    gameF_value_of_source_mex hcv hnotCarry (by omega) habsent hlower

  have hcol : c = v - 1 :=
    gameRecurrenceModel.fixed_q_injective hcv (by omega)
      (hcandidate.trans hstart.symm)
  dsimp [c] at hcol
  omega

/-- Apart from the predecessor value `v-1`, all lower openings satisfy the
owner bounds by arithmetic alone.  Thus excluding the predecessor's own
penultimate opening supplies the entire owner-coverage hypothesis. -/
theorem penultimateOwnerCovered_of_no_previous_penultimate
    {v : Nat} (hv : 3 <= v)
    (hprevious : gameF (v - 1) (v - 2) ≠ v - 1) :
    PenultimateOwnerCovered v := by
  intro k hkpos hkv
  rcases gameRecurrenceModel.opening_cover hkpos with
      ⟨a, hak, hdiag⟩ | ⟨r, hrk, hstart⟩
  · exact Or.inl ⟨a, by omega, hdiag⟩
  · by_cases hrc : r <= v - 3
    · exact Or.inr ⟨r, hrc, hrk, hstart⟩
    · have hk : k = v - 1 := by omega
      have hr : r = v - 2 := by omega
      subst k
      subst r
      exact False.elim (hprevious hstart)

/-- Conversely, the predecessor's penultimate opening destroys owner
coverage at exactly the value `v-1`: it is neither a diagonal value nor a
blocker with an earlier opening column. -/
theorem not_penultimateOwnerCovered_of_previous_penultimate
    {v : Nat} (hv : 3 <= v)
    (hprevious : gameF (v - 1) (v - 2) = v - 1) :
    Not (PenultimateOwnerCovered v) := by
  intro howners
  rcases howners (v - 1) (by omega) (by omega) with
      ⟨a, _ha, hdiag⟩ | ⟨r, hrc, hrk, hstart⟩
  · exact disjoint_D_S gameRecurrenceModel
      ⟨a, hdiag⟩ ⟨v - 2, by omega, hprevious⟩
  · have hrv : r = v - 2 :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hrk) (by omega)
        (hstart.trans hprevious.symm)
    omega

/-- Exact local meaning of the apparently global owner certificate. -/
theorem penultimateOwnerCovered_iff_no_previous_penultimate
    {v : Nat} (hv : 3 <= v) :
    PenultimateOwnerCovered v <->
      gameF (v - 1) (v - 2) ≠ v - 1 := by
  constructor
  · intro howners hprevious
    exact not_penultimateOwnerCovered_of_previous_penultimate hv
      hprevious howners
  · exact penultimateOwnerCovered_of_no_previous_penultimate hv

/-- A penultimate opening at `v` forces the same opening at `v-1`.
This is the contrapositive owner-coverage step hidden in the specialized
dense-prefix theorem. -/
theorem gameF_penultimate_freeze_forces_previous
    {v : Nat} (hv : 5 <= v)
    (hcurrent : gameF v (v - 1) = v) :
    gameF (v - 1) (v - 2) = v - 1 := by
  by_cases hprevious : gameF (v - 1) (v - 2) = v - 1
  · exact hprevious
  · exact False.elim
      (gameF_no_penultimate_freeze_of_owner_coverage_of_five hv hcurrent
        (penultimateOwnerCovered_of_no_previous_penultimate (by omega)
          hprevious))

/-- Global boundary exclusion.  Strong induction descends to value `4`,
whose diagonal owner is the proved base `gameF 2 2 = 4`; a row-start owner
at column `3` would violate the diagonal/row-start opening partition. -/
theorem gameF_no_penultimate_freeze
    {v : Nat} (hv : 5 <= v) :
    gameF v (v - 1) ≠ v := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
      intro hcurrent
      have hprevious :=
        gameF_penultimate_freeze_forces_previous hv hcurrent
      by_cases hv5 : v = 5
      · subst v
        have hrowstart : gameF 4 3 = 4 := by simpa using hprevious
        exact disjoint_D_S gameRecurrenceModel
          ⟨2, gameF_diag_two⟩ ⟨3, by omega, hrowstart⟩
      · have hprevFive : 5 <= v - 1 := by omega
        exact ih (v - 1) (by omega) hprevFive hprevious

/-- From value six onward the owner-coverage certificate is itself
unconditional; its sole predecessor obstruction has just been excluded. -/
theorem gameF_penultimateOwnerCovered
    {v : Nat} (hv : 6 <= v) :
    PenultimateOwnerCovered v := by
  apply (penultimateOwnerCovered_iff_no_previous_penultimate
    (v := v) (by omega)).2
  exact gameF_no_penultimate_freeze (v := v - 1) (by omega)

/-- `GapOneKill` in the paper-bank coordinates: no row-start opening may
occur one column below its row, from column two onward.  Columns two and
three are killed by the exact diagonal owners `3` and `4`; all later
columns are the global penultimate-freeze theorem. -/
theorem gameF_gap_one_kill
    {c : Nat} (hc : 2 <= c) :
    gameF (c + 1) c ≠ c + 1 := by
  intro hgapOne
  by_cases hc2 : c = 2
  · subst c
    exact disjoint_D_S gameRecurrenceModel
      ⟨1, gameF_one_one⟩ ⟨2, by omega, by simpa using hgapOne⟩
  by_cases hc3 : c = 3
  · subst c
    exact disjoint_D_S gameRecurrenceModel
      ⟨2, gameF_diag_two⟩ ⟨3, by omega, by simpa using hgapOne⟩
  have hno := gameF_no_penultimate_freeze
    (v := c + 1) (by omega)
  apply hno
  simpa [show c + 1 - 1 = c by omega] using hgapOne

/-- Sharp unconditional owner coverage.  At `v>=4`, the sole possible
coverage obstruction is exactly the `GapOneKill` cell with `c=v-2`. -/
theorem gameF_penultimateOwnerCovered_of_four
    {v : Nat} (hv : 4 <= v) :
    PenultimateOwnerCovered v := by
  apply (penultimateOwnerCovered_iff_no_previous_penultimate
    (v := v) (by omega)).2
  have hgap := gameF_gap_one_kill (c := v - 2) (by omega)
  simpa [show v - 2 + 1 = v - 1 by omega] using hgap

/-- Actual-game discharge of the explicit `GapOneKill` port in
`DensePrefixAggregateGapOneClosure`: aggregate cancellation forces the
rank-two freeze column to be `3`, and an actual opening of blocker `4`
there contradicts `gameF_gap_one_kill`. -/
theorem dense_rank_two_breaks_gameF_gapOne
    (c kappa : Nat -> Nat)
    (hPiZero : forall i, i < 2 ->
      c (i + 1) + kappa (i + 1) = 2 * (i + 1) - 1)
    (hAggregate :
      densePrefixSum (fun i => kappa (i + 1)) 2 <=
        densePrefixSum
          (fun h => 2 * (h + 1) - c (h + 1) - 1) 1)
    (hFreezeTwo : gameF 4 (c 2) = 4) : False := by
  have hForced := dense_prefix_aggregate_cancellation 1 c kappa
    (by
      intro i hi
      exact hPiZero i (by omega))
    (by simpa using hAggregate)
  have hcTwo : c 2 = 3 := by
    have h := hForced.2
    omega
  have hgap : gameF 4 3 = 4 := by simpa [hcTwo] using hFreezeTwo
  exact gameF_gap_one_kill (c := 3) (by omega) hgap

/-- In R37/R40 notation, the boundary `V1` arm is impossible from `s=4`
onward, independently of any dip hypothesis. -/
theorem gameF_no_boundary_v1_of_row_ge_four
    {s : Nat} (hs : 4 <= s) :
    gameF (s + 1) s ≠ s + 1 := by
  have h := gameF_no_penultimate_freeze (v := s + 1) (by omega)
  simpa [show s + 1 - 1 = s by omega] using h

/-- Every actual late-blocker first-gap obstruction starts at `s>=4`.
The small rows are excluded by the exact diagonals through row three and
the unconditional lower bound on the next diagonal. -/
theorem gameF_late_blocker_first_gap_row_ge_four
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    4 <= s := by
  have hgap := hLate.1
  have hnext := gameRecurrenceModel.diagonal_gt (s + 1)
  by_cases hs0 : s = 0
  · subst s
    change gameF 1 1 + 1 < gameF 0 0 at hgap
    rw [gameF_one_one, gameF_zero_zero] at hgap
    omega
  by_cases hs1 : s = 1
  · subst s
    change gameF 2 2 + 1 < gameF 1 1 at hgap
    rw [gameF_diag_two, gameF_one_one] at hgap
    omega
  by_cases hs2 : s = 2
  · subst s
    change gameF 3 3 + 1 < gameF 2 2 at hgap
    rw [gameF_diag_three, gameF_diag_two] at hgap
    omega
  by_cases hs3 : s = 3
  · subst s
    change gameF 4 4 + 1 < gameF 3 3 at hgap
    rw [gameF_diag_three] at hgap
    change 4 < gameF 4 4 at hnext
    omega
  omega

/-- R40's boundary late-blocker face is empty, with no extra lower-bound
hypothesis on the dip row. -/
theorem gameF_late_blocker_boundary_v1_impossible
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1) : False := by
  exact gameF_no_boundary_v1_of_row_ge_four
    (gameF_late_blocker_first_gap_row_ge_four hLate) hboundary

/-- The first-gap blocker's own opening is never penultimate.  This removes
the endpoint `r=z-1` from R37's late-freeze interval but does not otherwise
collapse that interval. -/
theorem gameF_late_blocker_first_gap_freeze_not_penultimate
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    exists r,
      s + 1 <= r /\
      r + 1 < DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s := by
  have hs := gameF_late_blocker_first_gap_row_ge_four hLate
  rcases hLate with
    ⟨_hgap, r, hrLate, hrz, hstart, _hOld, _hNew⟩
  have hzFive : 5 <= DipFirstGap gameRecurrenceModel s := by omega
  have hno := gameF_no_penultimate_freeze
    (v := DipFirstGap gameRecurrenceModel s) hzFive
  have hrNe : r ≠ DipFirstGap gameRecurrenceModel s - 1 := by
    intro hr
    subst r
    exact hno hstart
  exact ⟨r, hrLate, by omega, hstart⟩

/-- R37's late-blocker `V1` split therefore has only its high/R27-gap arm.
The first-gap blocker freeze `gameF z r=z` remains untouched. -/
theorem gameF_late_blocker_first_gap_has_R27_gap
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    let z := DipFirstGap gameRecurrenceModel s
    let q := gameF (s + 1) s
    exists r,
      r < z /\ gameF z r = z /\
      (s + 1 < q /\ q < z /\
        exists x,
          s + 1 < x /\ x < z /\ Not (C gameF x s z) /\
          (x <= r \/
            Not (B gameF x s z) \/
            exists a, s < a /\ a < x /\ gameF a s = z)) := by
  dsimp only
  rcases gameF_late_blocker_first_gap_v1_boundary_or_R27_gap hLate with
    ⟨r, hrz, hstart, hboundary | hhigh⟩
  · exact False.elim
      (gameF_late_blocker_boundary_v1_impossible hLate hboundary)
  · exact ⟨r, hrz, hstart, hhigh⟩

#print axioms gameF_penultimate_freeze_forces_previous
#print axioms penultimateOwnerCovered_iff_no_previous_penultimate
#print axioms gameF_no_penultimate_freeze
#print axioms gameF_penultimateOwnerCovered
#print axioms gameF_gap_one_kill
#print axioms gameF_penultimateOwnerCovered_of_four
#print axioms dense_rank_two_breaks_gameF_gapOne
#print axioms gameF_no_boundary_v1_of_row_ge_four
#print axioms gameF_late_blocker_boundary_v1_impossible
#print axioms gameF_late_blocker_first_gap_freeze_not_penultimate
#print axioms gameF_late_blocker_first_gap_has_R27_gap

end ChompLean
