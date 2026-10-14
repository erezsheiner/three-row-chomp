import R43ExtremalEventECapacityContradiction

set_option autoImplicit false

namespace ChompLean

/-!
R45: attack the four ordered old-row packet pairs in the first surviving
event-E source-defect layer.

At `z+2=2*s`, the source-capacity menu leaves only

* `(c,b0)=(s-2,s-3)`,
* `(c,b0)=(s-2,s-1)`,
* `(c,b0)=(s-1,s-3)`, or
* `(c,b0)=(s-1,s-2)`.

The first pair forces the distance-three cross.  The second pair has the
wrong order and therefore forces an additional earlier ride of `z`.  In the
two endpoint pairs, an unused column has a value below `z`; following that
value through the recurrence gives either an extra same-column carry, an
ordered diagonal echo, or a next-row rehost.

No additional path or ride-exclusion principle is used.
-/

/-- A lower unused-column value has one of three useful transitions:

* it is carried from the preceding row in the same column;
* it is a later past diagonal, producing an ordered diagonal echo; or
* it is rehosted in the next row.
-/
def DefectOneLowerTransition (s z g : Nat) : Prop :=
  let q := gameF s g
  0 < q ∧ q < z ∧
    ((q < s ∧ gameF (s - 1) g = q) ∨
      (∃ a, g < a ∧ a < s ∧ gameF a a = q) ∨
      C gameF (s + 1) (s + 1) q)

/-- The concrete cross, together with its lower ordered-echo owner. -/
def DefectOneDeepCross (s z : Nat) : Prop :=
  gameF (s - 2) (s - 3) = gameF (s - 1) (s - 2) ∧
    gameF (s - 1) (s - 3) = gameF (s - 2) (s - 2) ∧
    gameF (s - 2) (s - 2) < z

/-- The reversed adjacent pair forces a third ride of `z`; the new-row host
cannot reuse that ride's column. -/
def DefectOneReverseRide (s z b1 : Nat) : Prop :=
  gameF (s - 1) (s - 2) = z ∧ b1 ≠ s - 2

/-- An unused column in a row already containing `z,z+1,z+2` must carry a
strictly smaller value.  This is only row injectivity plus diagonal
maximality. -/
theorem unused_column_below_consecutive_row_top
    (M : RecurrenceModel) {s z g b c : Nat}
    (hg : g < s) (hb : b < s) (hc : c < s)
    (hgb : g ≠ b) (hgc : g ≠ c)
    (hBase : M.f s b = z)
    (hSucc : M.f s c = z + 1)
    (hDiag : M.f s s = z + 2) :
    M.f s g < z := by
  have hle := diagonalMaximal M (q := s) (s := g) (Nat.le_of_lt hg)
  have hneBase : M.f s g ≠ z := by
    intro heq
    apply hgb
    exact M.fixed_q_injective (Nat.le_of_lt hg) (Nat.le_of_lt hb)
      (heq.trans hBase.symm)
  have hneSucc : M.f s g ≠ z + 1 := by
    intro heq
    apply hgc
    exact M.fixed_q_injective (Nat.le_of_lt hg) (Nat.le_of_lt hc)
      (heq.trans hSucc.symm)
  have hneDiag : M.f s g ≠ z + 2 := by
    intro heq
    have hcols := M.fixed_q_injective
      (q := s) (b₁ := g) (b₂ := s)
      (Nat.le_of_lt hg) (Nat.le_refl _)
      (heq.trans hDiag.symm)
    omega
  rw [hDiag] at hle
  omega

/-- Recurrence trace of a lower unused-column value.  In the MEX branch, a
past diagonal can only own the value strictly to the right of the column;
otherwise it would already be a forbidden source of the current cell. -/
theorem gameF_lower_unused_column_transition
    {s z g : Nat}
    (hg : g < s)
    (hDiag : gameF s s = z + 2)
    (hNextDiag : gameF (s + 1) (s + 1) = z + 1)
    (hLower : gameF s g < z) :
    DefectOneLowerTransition s z g := by
  let q := gameF s g
  change 0 < q ∧ q < z ∧
    ((q < s ∧ gameF (s - 1) g = q) ∨
      (∃ a, g < a ∧ a < s ∧ gameF a a = q) ∨
      C gameF (s + 1) (s + 1) q)
  have hqPos : 0 < q := by
    have hgt := gameRecurrenceModel.value_gt_index
      (q := s) (r := g) (Nat.le_of_lt hg)
    change g < gameF s g at hgt
    dsimp [q]
    omega
  have hqz : q < z := by
    dsimp [q]
    exact hLower
  refine ⟨hqPos, hqz, ?_⟩
  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  by_cases hCarry : gameF (s - 1) g < s
  · have hfirst := hrec.1 (q := s) (r := g) hg hCarry
    left
    constructor
    · dsimp [q]
      rw [hfirst]
      exact hCarry
    · dsimp [q]
      exact hfirst.symm
  · have hbranch : ¬ (g < s ∧ gameF (s - 1) g < s) := by
      intro h
      exact hCarry h.2
    have hmex := hrec.2
      (q := s) (r := g) (Nat.le_of_lt hg) hbranch
    change IsMex (B gameF s g) q at hmex
    have hBNext : B gameF (s + 1) (s + 1) q := by
      apply gameRecurrenceModel.mex_no_skip (Nat.le_refl _)
      · exact gameRecurrenceModel.diagonal_gt (s + 1)
      · exact hqPos
      · change q < gameF (s + 1) (s + 1)
        rw [hNextDiag]
        omega
    rcases hBNext with hR | hC
    · rcases hR with ⟨a, ha, haValue⟩
      have hmin : min a (s + 1) = a :=
        Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at haValue
      have has : a < s := by
        by_cases hlt : a < s
        · exact hlt
        · have haEq : a = s := by omega
          subst a
          rw [hDiag] at haValue
          omega
      have hga : g < a := by
        by_cases hlt : g < a
        · exact hlt
        · have hag : a ≤ g := by omega
          exfalso
          apply hmex.2.1
          left
          refine ⟨a, has, ?_⟩
          rw [Nat.min_eq_left hag]
          exact haValue
      right
      left
      exact ⟨a, hga, has, haValue⟩
    · right
      right
      exact hC

/-- Full four-pair normal form for the defect-one event-E packet.

Every old-row pair now pays one of the desired certificates: a lower cross,
an additional `z` ride, or a lower transition (carry / ordered echo /
next-row rehost). -/
theorem gameF_margin_eventE_defect_one_pair_attack
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1))
    (hdefectOne : gameF (s + 1) (s + 1) + 1 = 2 * s) :
    let z := gameF (s + 1) (s + 1) - 1
    ∃ c b0 b1,
      c < s ∧ b0 < s ∧ b1 < s + 1 ∧
      c ≠ b0 ∧ b0 ≠ b1 ∧
      gameF s c = z + 1 ∧ gameF s b0 = z ∧
      gameF (s + 1) b1 = z ∧
      (b1 = s - 4 ∨ b1 = s - 3 ∨ b1 = s - 2 ∨
        b1 = s - 1 ∨ b1 = s) ∧
      ((c = s - 2 ∧ b0 = s - 3 ∧ DefectOneDeepCross s z) ∨
        (c = s - 2 ∧ b0 = s - 1 ∧ DefectOneReverseRide s z b1) ∨
        (c = s - 1 ∧ b0 = s - 3 ∧
          DefectOneLowerTransition s z (s - 2)) ∨
        (c = s - 1 ∧ b0 = s - 2 ∧
          DefectOneLowerTransition s z (s - 3))) := by
  let z := gameF (s + 1) (s + 1) - 1
  have hwindow := gameF_margin_eventE_strict_window
    hU hdip hmargin hnextDip
  have hsFive : 5 ≤ s := hwindow.1
  have hz : z + 2 = 2 * s := by
    dsimp [z]
    have hdiagPos := gameRecurrenceModel.diagonal_gt (s + 1)
    change s + 1 < gameF (s + 1) (s + 1) at hdiagPos
    omega
  have hNextDiag : gameF (s + 1) (s + 1) = z + 1 := by
    dsimp [z]
    have hdiagPos := gameRecurrenceModel.diagonal_gt (s + 1)
    change s + 1 < gameF (s + 1) (s + 1) at hdiagPos
    omega
  have hunit := hU s hdip
  change gameF (s + 1) (s + 1) + 1 = gameF s s at hunit
  have hDiag : gameF s s = z + 2 := by omega
  have hPastBelow : ∀ a, a < s → gameF a a < z := by
    intro a ha
    rcases hmargin with hs0 | ⟨j, hsj, hmarg⟩
    · omega
    · have haj : a ≤ j := by omega
      have hle := rmax_ge gameRecurrenceModel j a haj
      change gameF a a ≤ RMax gameRecurrenceModel j at hle
      change RMax gameRecurrenceModel j < z at hmarg
      omega
  have hzPos : 0 < z := by omega
  have hsz : s < z := by omega
  have hnotPast : ∀ a, a < s → gameF a a ≠ z := by
    intro a ha heq
    have hlt := hPastBelow a ha
    omega

  rcases gameF_margin_eventE_defect_one_packet_menu
      hU hdip hmargin hnextDip hdefectOne with
    ⟨c, b0, b1, hc, hb0, hb1, hcNe, hbNe,
      hSucc, hBase, hHost1, hcMenu, hb0Menu, hb1Menu⟩
  refine ⟨c, b0, b1, hc, hb0, hb1, hcNe, hbNe,
    hSucc, hBase, hHost1, hb1Menu, ?_⟩
  rcases hcMenu with hcDeep | hcLast
  · rcases hb0Menu with hbDeep | hb0Menu
    · left
      refine ⟨hcDeep, hbDeep, ?_⟩
      subst c
      subst b0
      have hcross := gameF_defect_one_deep_pair_forces_cross
        (s := s) (z := z) (by omega) hz hBase hSucc
      exact ⟨hcross.1, hcross.2, hPastBelow (s - 2) (by omega)⟩
    · rcases hb0Menu with hbMiddle | hbLast
      · exact False.elim (hcNe (hcDeep.trans hbMiddle.symm))
      · right
        left
        refine ⟨hcDeep, hbLast, ?_⟩
        subst c
        subst b0
        rcases consecutive_high_packet_order_or_prior_column_host
            gameRecurrenceModel hzPos hsz hc hb0 hSucc hBase hnotPast with
          horder | ⟨a, hca, has, haValue⟩
        · omega
        · have haEq : a = s - 1 := by omega
          subst a
          constructor
          · exact haValue
          · intro hb1Eq
            subst b1
            exact encoding_same_lower_no_repeat game_encodes
              (s := s - 2) (t₁ := s - 1) (t₂ := s + 1) (p := z)
              (by omega) (by omega) (by omega) haValue hHost1
  · rcases hb0Menu with hbDeep | hb0Menu
    · right
      right
      left
      refine ⟨hcLast, hbDeep, ?_⟩
      subst c
      subst b0
      have hLower : gameF s (s - 2) < z :=
        unused_column_below_consecutive_row_top gameRecurrenceModel
          (g := s - 2) (b := s - 3) (c := s - 1)
          (by omega) (by omega) (by omega)
          (by omega) (by omega) hBase hSucc hDiag
      exact gameF_lower_unused_column_transition
        (g := s - 2) (by omega) hDiag hNextDiag hLower
    · rcases hb0Menu with hbMiddle | hbLast
      · right
        right
        right
        refine ⟨hcLast, hbMiddle, ?_⟩
        subst c
        subst b0
        have hLower : gameF s (s - 3) < z :=
          unused_column_below_consecutive_row_top gameRecurrenceModel
            (g := s - 3) (b := s - 2) (c := s - 1)
            (by omega) (by omega) (by omega)
            (by omega) (by omega) hBase hSucc hDiag
        exact gameF_lower_unused_column_transition
          (g := s - 3) (by omega) hDiag hNextDiag hLower
      · exact False.elim (hcNe (hcLast.trans hbLast.symm))

#print axioms unused_column_below_consecutive_row_top
#print axioms gameF_lower_unused_column_transition
#print axioms gameF_margin_eventE_defect_one_pair_attack

end ChompLean
