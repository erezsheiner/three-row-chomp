import R39LagTwoPredecessorDichotomy

set_option autoImplicit false

namespace ChompLean

/-!
R56: an honest conditional form of the window-local path theorem.

The theorem below is purely about the diagonal sequence of a
`RecurrenceModel`.  It assumes unit-depth dips and, separately, a global
no-adjacent-dips hypothesis.  No R35 specialization is asserted.
-/

/-- No two consecutive diagonal steps are both strict descents. -/
def NoAdjacentDiagonalDips (M : RecurrenceModel) : Prop :=
  forall i,
    M.f (i + 1) (i + 1) < M.f i i ->
    Not (M.f (i + 2) (i + 2) < M.f (i + 1) (i + 1))

/-- At a unit dip `D,D-1`, any diagonal owner of the fresh successor
`D+1` is forced to one of the next two local rows.

The hypotheses are deliberately stronger than the guarded R35 package:
`hNoAdjacent` applies at every index used by the path argument.
-/
theorem window_local_successor_owner
    (M : RecurrenceModel)
    (hU : UnitDip M)
    (hNoAdjacent : NoAdjacentDiagonalDips M)
    {s a : Nat}
    (hdip : M.f (s + 1) (s + 1) < M.f s s)
    (howner : M.f a a = M.f s s + 1) :
    a = s + 2 \/ a = s + 3 := by
  have hunitS : M.f (s + 1) (s + 1) + 1 = M.f s s :=
    hU s hdip

  have hfuture : s + 2 <= a := by
    apply Nat.le_of_not_gt
    intro haEarly
    have haCases : a < s \/ a = s \/ a = s + 1 := by omega
    rcases haCases with haPast | haNow | haDip
    · by_cases hfar : a + 2 <= s
      · exact (noDelayedDiagonalPredecessor_of_unitDip M hU hfar) howner
      · have haNext : a + 1 = s := by omega
        have haNext2 : a + 2 = s + 1 := by omega
        have hprevDip : M.f (a + 1) (a + 1) < M.f a a := by
          rw [haNext, howner]
          omega
        have hnotNext := hNoAdjacent a hprevDip
        apply hnotNext
        rw [haNext, haNext2]
        exact hdip
    · subst a
      omega
    · subst a
      omega

  by_cases ha2 : a = s + 2
  · exact Or.inl ha2

  have hs2a : s + 2 < a := by omega

  /- The first row after the dip is already strictly above `D+1` unless
  it is the owner itself. -/
  have hnotSecondDip :
      Not (M.f (s + 2) (s + 2) < M.f (s + 1) (s + 1)) :=
    hNoAdjacent s hdip
  have hneConsecutive :
      M.f (s + 2) (s + 2) ≠ M.f (s + 1) (s + 1) := by
    intro hEq
    have hidx := diagonal_injective M hEq
    omega
  have hpostDipRise :
      M.f (s + 1) (s + 1) < M.f (s + 2) (s + 2) := by
    omega
  have hneOldDiagonal : M.f (s + 2) (s + 2) ≠ M.f s s := by
    intro hEq
    have hidx := diagonal_injective M hEq
    omega
  have hneOwnerValue :
      M.f (s + 2) (s + 2) ≠ M.f s s + 1 := by
    intro hEq
    have hdiagEq : M.f (s + 2) (s + 2) = M.f a a :=
      hEq.trans howner.symm
    have hidx := diagonal_injective M hdiagEq
    omega
  have hbase : M.f s s + 1 < M.f (s + 2) (s + 2) := by
    omega

  /- Before the owner row, the diagonal cannot fall to `D+1` or below.
  A first such fall would be a unit dip landing exactly on `D+1`, hence
  would repeat the alleged owner value at an earlier row. -/
  have hAbove : forall n,
      s + 2 + n < a ->
      M.f s s + 1 < M.f (s + 2 + n) (s + 2 + n) := by
    intro n
    induction n with
    | zero =>
        intro _hlt
        simpa using hbase
    | succ n ih =>
        intro hlt
        have hprevLt : s + 2 + n < a := by omega
        have hprev := ih hprevLt
        apply Nat.lt_of_not_ge
        intro hlow
        have hdipStep :
            M.f (s + 2 + (n + 1)) (s + 2 + (n + 1)) <
              M.f (s + 2 + n) (s + 2 + n) := by
          omega
        have hunitStep :
            M.f (s + 2 + (n + 1)) (s + 2 + (n + 1)) + 1 =
              M.f (s + 2 + n) (s + 2 + n) := by
          simpa [Nat.add_assoc] using hU (s + 2 + n) (by
            simpa [Nat.add_assoc] using hdipStep)
        have hnextEq :
            M.f (s + 2 + (n + 1)) (s + 2 + (n + 1)) =
              M.f s s + 1 := by
          omega
        have hdiagEq :
            M.f (s + 2 + (n + 1)) (s + 2 + (n + 1)) = M.f a a :=
          hnextEq.trans howner.symm
        have hidx := diagonal_injective M hdiagEq
        omega

  let n := a - (s + 3)
  have ha : a = s + 3 + n := by
    dsimp [n]
    omega
  have hpredAbove :
      M.f s s + 1 < M.f (s + 2 + n) (s + 2 + n) :=
    hAbove n (by omega)
  have howner' :
      M.f (s + 3 + n) (s + 3 + n) = M.f s s + 1 := by
    rw [← ha]
    exact howner
  have hnextIndex : s + 2 + n + 1 = s + 3 + n := by omega
  have hfinalDip :
      M.f ((s + 2 + n) + 1) ((s + 2 + n) + 1) <
        M.f (s + 2 + n) (s + 2 + n) := by
    rw [hnextIndex, howner']
    exact hpredAbove
  have hpredEq :
      M.f (s + 2 + n) (s + 2 + n) = M.f s s + 2 := by
    have hfinalUnit := hU (s + 2 + n) hfinalDip
    rw [hnextIndex, howner'] at hfinalUnit
    omega

  by_cases hn : n = 0
  · exact Or.inr (by omega)
  · let m := n - 1
    have hnEq : n = m + 1 := by
      dsimp [m]
      omega
    have hprevAbove :
        M.f s s + 1 < M.f (s + 2 + m) (s + 2 + m) :=
      hAbove m (by omega)
    have hpredEq' :
        M.f (s + 2 + (m + 1)) (s + 2 + (m + 1)) = M.f s s + 2 := by
      rw [← hnEq]
      exact hpredEq
    have hfinalDip' :
        M.f ((s + 2 + (m + 1)) + 1) ((s + 2 + (m + 1)) + 1) <
          M.f (s + 2 + (m + 1)) (s + 2 + (m + 1)) := by
      rw [← hnEq]
      exact hfinalDip
    have hnePred :
        M.f (s + 2 + m) (s + 2 + m) ≠
          M.f (s + 2 + (m + 1)) (s + 2 + (m + 1)) := by
      intro hEq
      have hidx := diagonal_injective M hEq
      omega
    have hdipIntoPred :
        M.f (s + 2 + (m + 1)) (s + 2 + (m + 1)) <
          M.f (s + 2 + m) (s + 2 + m) := by
      omega
    have hnotFinalDip := hNoAdjacent (s + 2 + m) (by
      simpa [Nat.add_assoc] using hdipIntoPred)
    apply False.elim
    apply hnotFinalDip
    simpa [Nat.add_assoc] using hfinalDip'

/-- Split form: there is no past owner and no owner at row `s+4` or later. -/
theorem window_local_successor_owner_bounds
    (M : RecurrenceModel)
    (hU : UnitDip M)
    (hNoAdjacent : NoAdjacentDiagonalDips M)
    {s a : Nat}
    (hdip : M.f (s + 1) (s + 1) < M.f s s)
    (howner : M.f a a = M.f s s + 1) :
    Not (a < s) /\ Not (s + 4 <= a) := by
  have hlocal :=
    window_local_successor_owner M hU hNoAdjacent hdip howner
  rcases hlocal with rfl | rfl <;> omega

/-- Exact local anatomy of the two surviving owner rows.  The `s+2`
owner is reached by a rise of two from the dipped value.  The `s+3`
owner is reached after a rise of three and then one unit dip. -/
theorem window_local_successor_owner_anatomy
    (M : RecurrenceModel)
    (hU : UnitDip M)
    (hNoAdjacent : NoAdjacentDiagonalDips M)
    {s a : Nat}
    (hdip : M.f (s + 1) (s + 1) < M.f s s)
    (howner : M.f a a = M.f s s + 1) :
    (a = s + 2 /\
      M.f (s + 2) (s + 2) = M.f (s + 1) (s + 1) + 2) \/
    (a = s + 3 /\
      M.f (s + 2) (s + 2) = M.f (s + 1) (s + 1) + 3 /\
      M.f (s + 3) (s + 3) + 1 = M.f (s + 2) (s + 2)) := by
  have hunitS := hU s hdip
  rcases window_local_successor_owner M hU hNoAdjacent hdip howner with
    ha2 | ha3
  · subst a
    exact Or.inl ⟨rfl, by omega⟩
  · subst a
    have hnotSecondDip :
        Not (M.f (s + 2) (s + 2) < M.f (s + 1) (s + 1)) :=
      hNoAdjacent s hdip
    have hneConsecutive :
        M.f (s + 2) (s + 2) ≠ M.f (s + 1) (s + 1) := by
      intro hEq
      have hidx := diagonal_injective M hEq
      omega
    have hpostDipRise :
        M.f (s + 1) (s + 1) < M.f (s + 2) (s + 2) := by
      omega
    have hneOldDiagonal : M.f (s + 2) (s + 2) ≠ M.f s s := by
      intro hEq
      have hidx := diagonal_injective M hEq
      omega
    have hneOwnerRow :
        M.f (s + 2) (s + 2) ≠ M.f (s + 3) (s + 3) := by
      intro hEq
      have hidx := diagonal_injective M hEq
      omega
    have hdipIntoOwner :
        M.f (s + 3) (s + 3) < M.f (s + 2) (s + 2) := by
      omega
    have hunitIntoOwner := hU (s + 2) hdipIntoOwner
    have hunitIntoOwner' :
        M.f (s + 3) (s + 3) + 1 = M.f (s + 2) (s + 2) := by
      simpa [Nat.add_assoc] using hunitIntoOwner
    exact Or.inr ⟨rfl, by omega, hunitIntoOwner'⟩

#print axioms window_local_successor_owner
#print axioms window_local_successor_owner_bounds
#print axioms window_local_successor_owner_anatomy

end ChompLean
