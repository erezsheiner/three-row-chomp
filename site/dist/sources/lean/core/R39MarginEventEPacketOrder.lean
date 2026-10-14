import R36MarginEventETwoRideCertificate

set_option autoImplicit false

namespace ChompLean

/-!
R39: a column-order audit of the numerical-margin event-E packet.

No RM2 and no no-two-ride principle is used.  The key observation is that
the cell carrying `z+1` must cover `z`.  Hence either the known current-row
`z` cell is to its left, or the coverage comes from an earlier row in the
same column.  In the latter case event E already contains a third ride.
-/

/-- Two consecutive high values in one row have the expected column order,
unless the lower value was already hosted in the upper value's column on an
earlier row. -/
theorem consecutive_high_packet_order_or_prior_column_host
    (M : RecurrenceModel) {s z c b : Nat}
    (hzpos : 0 < z) (hsz : s < z)
    (hc : c < s) (hb : b < s)
    (hsucc : M.f s c = z + 1) (hbase : M.f s b = z)
    (hnotPast : forall a, a < s -> M.f a a ≠ z) :
    b < c \/ exists a, c < a /\ a < s /\ M.f a c = z := by
  have hB : B M.f s c z := by
    apply M.mex_no_skip (Nat.le_of_lt hc)
    · rw [hsucc]
      omega
    · exact hzpos
    · rw [hsucc]
      omega
  rcases hB with hR | hC
  · right
    rcases hR with ⟨a, ha, hvalue⟩
    by_cases hac : a <= c
    · have hmin : min a c = a := Nat.min_eq_left hac
      rw [hmin] at hvalue
      exact False.elim ((hnotPast a ha) hvalue)
    · have hca : c < a := by omega
      have hmin : min a c = c := Nat.min_eq_right (by omega)
      rw [hmin] at hvalue
      exact ⟨a, hca, ha, hvalue⟩
  · left
    rcases hC with ⟨b', hb'c, hvalue⟩
    have hb'Eq : b' = b := by
      exact M.fixed_q_injective (by omega) (by omega)
        (hvalue.trans hbase.symm)
    omega

/-- If both `z` and `z+1` occur before `V1` in a row whose diagonal is
`z+2`, the actual `V1` output is a new lower packet.  It is not a past
diagonal and is necessarily rehosted on the following `z+1` diagonal row.
-/
theorem two_high_values_before_v1_create_lower_next_row_packet
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f)
    {s z c b : Nat}
    (hc : c + 1 < s) (hb : b < c)
    (hsucc : M.f s c = z + 1) (hbase : M.f s b = z)
    (hdiag : M.f s s = z + 2)
    (hnextDiag : M.f (s + 1) (s + 1) = z + 1) :
    let q := M.f s (s - 1)
    0 < q /\ q < z /\
      (forall a, a < s -> M.f a a ≠ q) /\
      C M.f (s + 1) (s + 1) q := by
  dsimp only
  let q := M.f s (s - 1)
  have hspos : 0 < s := by omega
  have hpred : s - 1 < M.f (s - 1) (s - 1) :=
    M.diagonal_gt (s - 1)
  have hbranch :
      Not (s - 1 < s /\ M.f (s - 1) (s - 1) < s) := by
    omega
  have hmexQ0 := hrec.2 (q := s) (r := s - 1) (by omega) hbranch
  have hmexQ : IsMex (B M.f s (s - 1)) q := by
    simpa [q] using hmexQ0
  have hqpos : 0 < q := hmexQ.1
  have hbLast : b < s - 1 := by omega
  have hcLast : c < s - 1 := by omega
  have hzSource : B M.f s (s - 1) z :=
    Or.inr ⟨b, hbLast, hbase⟩
  have hsuccSource : B M.f s (s - 1) (z + 1) :=
    Or.inr ⟨c, hcLast, hsucc⟩
  have hqNeZ : q ≠ z := by
    intro hEq
    exact hmexQ.2.1 (by simpa [hEq] using hzSource)
  have hqNeSucc : q ≠ z + 1 := by
    intro hEq
    exact hmexQ.2.1 (by simpa [hEq] using hsuccSource)
  have hqLeDiag : q <= M.f s s :=
    diagonalMaximal M (q := s) (s := s - 1) (by omega)
  have hqNeDiag : q ≠ M.f s s := by
    intro hEq
    have hcols := M.fixed_q_injective
      (q := s) (b₁ := s - 1) (b₂ := s)
      (by omega) (Nat.le_refl _) hEq
    omega
  have hqltDiag : q < M.f s s := by omega
  have hqz : q < z := by
    rw [hdiag] at hqltDiag
    omega
  have hqNotPast : forall a, a < s -> M.f a a ≠ q := by
    intro a ha hvalue
    apply hmexQ.2.1
    left
    refine ⟨a, ha, ?_⟩
    have hale : a <= s - 1 := by omega
    simpa [Nat.min_eq_left hale] using hvalue
  have hqBNext : B M.f (s + 1) (s + 1) q := by
    apply M.mex_no_skip (Nat.le_refl _) (M.diagonal_gt _) hqpos
    rw [hnextDiag]
    omega
  have hqCNext : C M.f (s + 1) (s + 1) q := by
    rcases hqBNext with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hmin : min a (s + 1) = a :=
        Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at hvalue
      by_cases has : a < s
      · exact False.elim ((hqNotPast a has) hvalue)
      · have haEq : a = s := by omega
        subst a
        rw [hdiag] at hvalue
        omega
    · exact hC
  exact ⟨hqpos, hqz, hqNotPast, hqCNext⟩

/-- Event-E packet sharpening.  If the `z+1` packet is not already at the
pre-dip `V1` column, then either:

* `z` had an additional earlier ride in that same packet column; or
* the current-row packet is correctly ordered and creates a new lower
  non-diagonal packet which must be rehosted on the dip row.

Thus failure of the first first-eligible condition cannot be silent. -/
theorem gameF_margin_eventE_zsucc_not_v1_forces_extra_packet
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip : gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let z := gameF (s + 1) (s + 1) - 1
    exists c b0 b1,
      c < s /\ b0 < s /\ b1 < s + 1 /\
      gameF s c = z + 1 /\ gameF s b0 = z /\
      gameF (s + 1) b1 = z /\
      (c + 1 = s \/
        (exists a, c < a /\ a < s /\ gameF a c = z /\ c ≠ b1) \/
        (let q := gameF s (s - 1)
         0 < q /\ q < z /\
           (forall a, a < s -> gameF a a ≠ q) /\
           C gameF (s + 1) (s + 1) q)) := by
  let z := gameF (s + 1) (s + 1) - 1
  rcases gameF_margin_eventE_has_three_cell_entry_packet
      hU hdip hmargin hnextDip with
    ⟨c, b0, b1, hc, hb0, hb1, _hcNe, _hbNe,
      hsucc, hbase, hhost1, hEmit⟩
  refine ⟨c, b0, b1, hc, hb0, hb1, hsucc, hbase, hhost1, ?_⟩
  by_cases hcLast : c + 1 = s
  · exact Or.inl hcLast
  · have hcBefore : c + 1 < s := by omega
    have hzpos : 0 < z := by
      dsimp [z]
      have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
      change s + 1 < gameF (s + 1) (s + 1) at hgt
      omega
    have hs1z : s + 1 < z := by
      have hgt := gameRecurrenceModel.diagonal_gt (s + 2)
      change s + 2 < gameF (s + 2) (s + 2) at hgt
      rw [hEmit] at hgt
      omega
    have hsz : s < z := by omega
    have hnotPast : forall a, a < s -> gameF a a ≠ z := by
      intro a ha
      exact margin_guard_hole_not_past
        gameRecurrenceModel hdip hmargin a (by omega)
    rcases consecutive_high_packet_order_or_prior_column_host
        gameRecurrenceModel hzpos hsz hc hb0 hsucc hbase hnotPast with
      horder | hprior
    · right
      right
      have hunitPrev := hU s hdip
      change gameF (s + 1) (s + 1) + 1 = gameF s s at hunitPrev
      have hdiagS : gameF s s = z + 2 := by
        dsimp [z]
        omega
      have hdiagNext : gameF (s + 1) (s + 1) = z + 1 := by
        dsimp [z]
        have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
        omega
      have hrec : BrouwerRecurrence gameF :=
        recurrence_of_encoding_and_mex game_encodes game_complete
          (mex_branch_of_encoding_and_lower game_encodes game_complete
            game_lower_blocked)
      exact two_high_values_before_v1_create_lower_next_row_packet
        gameRecurrenceModel hrec hcBefore horder hsucc hbase
          hdiagS hdiagNext
    · right
      left
      rcases hprior with ⟨a, hca, has, hvalue⟩
      have hcNeB1 : c ≠ b1 := by
        intro hEq
        subst b1
        exact encoding_same_lower_no_repeat game_encodes
          hca (by omega) hs1z hvalue hhost1
      exact ⟨a, hca, has, hvalue, hcNeB1⟩

#print axioms consecutive_high_packet_order_or_prior_column_host
#print axioms two_high_values_before_v1_create_lower_next_row_packet
#print axioms gameF_margin_eventE_zsucc_not_v1_forces_extra_packet

end ChompLean
