import R34MarginEventEEquivalence

set_option autoImplicit false

namespace ChompLean

/-!
Concrete actual-game certificate for the remaining numerical-margin event E.

If a unit dip at `s+1` is followed immediately by another dip, put
`z=d(s+1)-1`.  Numerical margin removes every historical diagonal owner of
`z`.  Exact diagonal MEX coverage therefore forces `z` into the strict row
prefix on both rows `s` and `s+1`; the second unit dip emits it at `s+2`.
The actual encoding's same-lower no-repeat law makes the two host columns
distinct.  Thus event E is literally a two-ride-then-emit event.
-/

/-- A numerical-margin consecutive dip yields two distinct consecutive-row
hosts followed by diagonal emission, with the emitted value absent from its
own diagonal source.  No RM2 hypothesis is used. -/
theorem gameF_margin_eventE_has_two_ride_then_emit_certificate
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip : gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let z := gameF (s + 1) (s + 1) - 1
    ∃ b₀ b₁,
      b₀ < s ∧ b₁ < s + 1 ∧ b₀ ≠ b₁ ∧
      gameF s b₀ = z ∧ gameF (s + 1) b₁ = z ∧
      gameF (s + 2) (s + 2) = z ∧
      ¬ B gameF (s + 2) (s + 2) z := by
  let z := gameF (s + 1) (s + 1) - 1
  have hzPos : 0 < z := by
    dsimp [z]
    have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
    change s + 1 < gameF (s + 1) (s + 1) at hgt
    omega
  have hunitPrev :
      gameF (s + 1) (s + 1) + 1 = gameF s s :=
    hU s hdip
  have hunitNextRaw := hU (s + 1) hnextDip
  have hunitNext :
      gameF (s + 2) (s + 2) + 1 =
        gameF (s + 1) (s + 1) := by
    simpa [Nat.add_assoc] using hunitNextRaw
  have hEmit : gameF (s + 2) (s + 2) = z := by
    dsimp [z]
    omega
  have hnotPast :
      ∀ i, i ≤ s → gameF i i ≠ z := by
    intro i his
    exact margin_guard_hole_not_past
      gameRecurrenceModel hdip hmargin i his
  have hzBelowPrev : z < gameF s s := by
    dsimp [z]
    omega
  have hBPrev : B gameF s s z :=
    gameRecurrenceModel.mex_no_skip (Nat.le_refl s)
      (gameRecurrenceModel.diagonal_gt s) hzPos hzBelowPrev
  have hCPrev : C gameF s s z := by
    rcases hBPrev with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hmin : min a s = a := Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at hvalue
      exact False.elim (hnotPast a (by omega) hvalue)
    · exact hC
  have hzBelowDip : z < gameF (s + 1) (s + 1) := by
    dsimp [z]
    have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
    omega
  have hBDip : B gameF (s + 1) (s + 1) z :=
    gameRecurrenceModel.mex_no_skip (Nat.le_refl (s + 1))
      (gameRecurrenceModel.diagonal_gt (s + 1)) hzPos hzBelowDip
  have hCDip : C gameF (s + 1) (s + 1) z := by
    rcases hBDip with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hmin : min a (s + 1) = a :=
        Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at hvalue
      exact False.elim (hnotPast a (by omega) hvalue)
    · exact hC
  rcases hCPrev with ⟨b₀, hb₀, hhost₀⟩
  rcases hCDip with ⟨b₁, hb₁, hhost₁⟩
  have hsBelowZ : s + 1 < z := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 2)
    change s + 2 < gameF (s + 2) (s + 2) at hgt
    rw [hEmit] at hgt
    omega
  have hbNe : b₀ ≠ b₁ := by
    intro hEq
    subst b₁
    exact encoding_same_lower_no_repeat game_encodes
      hb₀ (by omega) hsBelowZ hhost₀ hhost₁
  have hAbsent : ¬ B gameF (s + 2) (s + 2) z := by
    have hmex := recurrence_diagonal_exact_mex
      gameRecurrenceModel (s + 2)
    change IsMex (B gameF (s + 2) (s + 2))
      (gameF (s + 2) (s + 2)) at hmex
    rw [hEmit] at hmex
    exact hmex.2.1
  exact ⟨b₀, b₁, hb₀, hb₁, hbNe, hhost₀, hhost₁,
    hEmit, hAbsent⟩

/-- Event E carries a three-cell entry packet before the final emission:
the preceding row contains both `z+1` and `z`, in distinct columns, and the
dip row contains `z` again in a new column.  MEX fixes the three values;
the still-open first-eligible law is exactly what would pin their columns to
`V1,V2,V1`. -/
theorem gameF_margin_eventE_has_three_cell_entry_packet
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip : gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let z := gameF (s + 1) (s + 1) - 1
    ∃ c b₀ b₁,
      c < s ∧ b₀ < s ∧ b₁ < s + 1 ∧
      c ≠ b₀ ∧ b₀ ≠ b₁ ∧
      gameF s c = z + 1 ∧ gameF s b₀ = z ∧
      gameF (s + 1) b₁ = z ∧
      gameF (s + 2) (s + 2) = z := by
  let z := gameF (s + 1) (s + 1) - 1
  rcases gameF_margin_eventE_has_two_ride_then_emit_certificate
      hU hdip hmargin hnextDip with
    ⟨b₀, b₁, hb₀, hb₁, hbNe, hhost₀, hhost₁, hEmit, _⟩
  have hzPos : 0 < z := by
    dsimp [z]
    have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
    change s + 1 < gameF (s + 1) (s + 1) at hgt
    omega
  have hunitPrev :
      gameF (s + 1) (s + 1) + 1 = gameF s s :=
    hU s hdip
  have hSuccBelow : z + 1 < gameF s s := by
    dsimp [z]
    omega
  have hnotPastSucc : ∀ a, a < s → gameF a a ≠ z + 1 := by
    intro a has haEq
    rcases hmargin with hs0 | ⟨j, hsj, hmargin⟩
    · omega
    · have haj : a ≤ j := by omega
      have hle := rmax_ge gameRecurrenceModel j a haj
      change gameF a a ≤ RMax gameRecurrenceModel j at hle
      rw [haEq] at hle
      omega
  have hBSucc : B gameF s s (z + 1) :=
    gameRecurrenceModel.mex_no_skip (Nat.le_refl s)
      (gameRecurrenceModel.diagonal_gt s) (by omega) hSuccBelow
  have hCSucc : C gameF s s (z + 1) := by
    rcases hBSucc with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hmin : min a s = a := Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at hvalue
      exact False.elim (hnotPastSucc a ha hvalue)
    · exact hC
  rcases hCSucc with ⟨c, hc, hhostSucc⟩
  have hcNe : c ≠ b₀ := by
    intro hEq
    subst c
    rw [hhost₀] at hhostSucc
    omega
  exact ⟨c, b₀, b₁, hc, hb₀, hb₁, hcNe, hbNe,
    hhostSucc, hhost₀, hhost₁, hEmit⟩

/-- Global scheduler form suggested by the failure census: a value cannot
ride in two consecutive rows (in distinct columns) and then become the next
diagonal emission.  This is deliberately named as an open law, not assumed
to follow from no-repeat alone. -/
def NoTwoRideThenDiagonalEmit (f : Nat → Nat → Nat) : Prop :=
  ∀ {s z b₀ b₁},
    b₀ < s → b₁ < s + 1 → b₀ ≠ b₁ →
    f s b₀ = z → f (s + 1) b₁ = z →
    f (s + 2) (s + 2) = z → False

/-- The global no-two-ride scheduler law eliminates event E at every
numerical-margin site. -/
theorem gameF_marginNoConsecutiveDips_of_noTwoRideThenDiagonalEmit
    (hU : UnitDip gameRecurrenceModel)
    (hNoRide : NoTwoRideThenDiagonalEmit gameF) :
    MarginNoConsecutiveDips gameRecurrenceModel := by
  intro s hdip hmargin hnextDip
  rcases gameF_margin_eventE_has_two_ride_then_emit_certificate
      hU hdip hmargin hnextDip with
    ⟨b₀, b₁, hb₀, hb₁, hbNe, hhost₀, hhost₁, hEmit, _hAbsent⟩
  exact hNoRide hb₀ hb₁ hbNe hhost₀ hhost₁ hEmit

/-- RM2 reduction through the concrete two-ride-then-emit scheduler atom. -/
theorem game_twoStepRecordLaw_of_unitDip_noTwoRideThenDiagonalEmit
    (hU : UnitDip gameRecurrenceModel)
    (hNoRide : NoTwoRideThenDiagonalEmit gameF) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel :=
  twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
    gameRecurrenceModel hU
      (gameF_marginNoConsecutiveDips_of_noTwoRideThenDiagonalEmit
        hU hNoRide)

#print axioms gameF_margin_eventE_has_two_ride_then_emit_certificate
#print axioms gameF_margin_eventE_has_three_cell_entry_packet
#print axioms game_twoStepRecordLaw_of_unitDip_noTwoRideThenDiagonalEmit

end ChompLean
