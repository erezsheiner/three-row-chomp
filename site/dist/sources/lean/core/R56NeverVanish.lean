import R55Integration

set_option autoImplicit false

namespace ChompLean

/-!
R56: exact audit of the proposed NEVER-VANISH statement.

The relevant conclusion is already forced by the diagonal MEX in every
`RecurrenceModel`.  If `v` is positive, strictly below the diagonal on row
`q`, and is not any earlier diagonal value, the historical branch of the
diagonal source is impossible.  Exact MEX therefore places `v` in the
strict row prefix of row `q`.

This is stronger than a no-vanish implication: it does not assume that `v`
was present on the preceding row.  Consequently the finite receipt saying
that a non-past value below the next diagonal never disappears is already a
theorem under its stated guards.

We deliberately do not introduce a `third hole of Sigma` predicate here.
That terminology needs a separate exact definition of `Sigma` and a proof
identifying its first two positive holes.  For the claimed application the
stronger fact below makes the all-row-absent side impossible directly.
-/

/-- A value occurs in the triangular part of row `q`, including its
diagonal cell. -/
def RowPresent (f : Nat -> Nat -> Nat) (q v : Nat) : Prop :=
  exists b, b <= q /\ f q b = v

/-- A value is absent from every triangular cell of row `q`. -/
def RowAbsent (f : Nat -> Nat -> Nat) (q v : Nat) : Prop :=
  Not (RowPresent f q v)

/-- The value is the diagonal value of a strictly earlier row. -/
def PastDiagonalValueBefore (M : RecurrenceModel) (q v : Nat) : Prop :=
  exists a, a < q /\ M.f a a = v

/-- All-row absence is exactly absence from the strict prefix together with
inequality to the diagonal value. -/
theorem rowAbsent_iff_no_strict_prefix_and_not_diagonal
    {f : Nat -> Nat -> Nat} {q v : Nat} :
    RowAbsent f q v <-> Not (C f q q v) /\ f q q ≠ v := by
  constructor
  · intro hAbsent
    constructor
    · rintro ⟨b, hbq, hvalue⟩
      exact hAbsent ⟨b, Nat.le_of_lt hbq, hvalue⟩
    · intro hdiag
      exact hAbsent ⟨q, Nat.le_refl q, hdiag⟩
  · rintro ⟨hPrefix, hdiag⟩ ⟨b, hbq, hvalue⟩
    by_cases hlt : b < q
    · exact hPrefix ⟨b, hlt, hvalue⟩
    · have hbeq : b = q := by omega
      subst b
      exact hdiag hvalue

/-- Strong unconditional NEVER-VANISH core.

The conclusion is strict-prefix presence, stronger than mere row presence.
The proof uses the exact diagonal MEX theorem.  Its historical-source case
would make `v` an earlier diagonal, so only the current-row source remains.
-/
theorem recurrence_nonpast_below_diagonal_strict_prefix
    (M : RecurrenceModel) {q v : Nat}
    (hvPos : 0 < v)
    (hvBelow : v < M.f q q)
    (hvNonpast : Not (PastDiagonalValueBefore M q v)) :
    C M.f q q v := by
  have hMex : IsMex (B M.f q q) (M.f q q) :=
    recurrence_diagonal_exact_mex M q
  have hBlocked : B M.f q q v := hMex.2.2 v hvPos hvBelow
  rcases hBlocked with hHistory | hPrefix
  · exfalso
    apply hvNonpast
    rcases hHistory with ⟨a, haq, hvalue⟩
    refine ⟨a, haq, ?_⟩
    simpa [Nat.min_eq_left (Nat.le_of_lt haq)] using hvalue
  · exact hPrefix

/-- Row-presence form of the strict-prefix theorem. -/
theorem recurrence_nonpast_below_diagonal_row_present
    (M : RecurrenceModel) {q v : Nat}
    (hvPos : 0 < v)
    (hvBelow : v < M.f q q)
    (hvNonpast : Not (PastDiagonalValueBefore M q v)) :
    RowPresent M.f q v := by
  rcases recurrence_nonpast_below_diagonal_strict_prefix
      M hvPos hvBelow hvNonpast with ⟨b, hbq, hvalue⟩
  exact ⟨b, Nat.le_of_lt hbq, hvalue⟩

/-- In particular, a value satisfying the guards at row `t+1` cannot be
present on row `t` and absent from all of row `t+1`.  The old-row presence
hypothesis is intentionally unused by the stronger core theorem. -/
theorem recurrence_nonpast_below_next_diagonal_cannot_vanish
    (M : RecurrenceModel) {t v : Nat}
    (hvPos : 0 < v)
    (hvBelow : v < M.f (t + 1) (t + 1))
    (hvNonpast : Not (PastDiagonalValueBefore M (t + 1) v)) :
    Not (RowPresent M.f t v /\ RowAbsent M.f (t + 1) v) := by
  intro hVanish
  have hNext : RowPresent M.f (t + 1) v :=
    recurrence_nonpast_below_diagonal_row_present
      M hvPos hvBelow hvNonpast
  exact hVanish.2 hNext

/-- Actual-game specialization, stated without the model projection. -/
theorem gameF_nonpast_below_next_diagonal_row_present
    {t v : Nat}
    (hvPos : 0 < v)
    (hvBelow : v < gameF (t + 1) (t + 1))
    (hvNonpast : Not (exists a, a < t + 1 /\ gameF a a = v)) :
    RowPresent gameF (t + 1) v := by
  apply recurrence_nonpast_below_diagonal_row_present
      gameRecurrenceModel hvPos hvBelow
  simpa [PastDiagonalValueBefore, gameRecurrenceModel] using hvNonpast

/-- Receipt-facing actual-game no-vanish corollary. -/
theorem gameF_nonpast_below_next_diagonal_cannot_vanish
    {t v : Nat}
    (hvPos : 0 < v)
    (hvBelow : v < gameF (t + 1) (t + 1))
    (hvNonpast : Not (exists a, a < t + 1 /\ gameF a a = v)) :
    Not (RowPresent gameF t v /\ RowAbsent gameF (t + 1) v) := by
  intro hVanish
  exact hVanish.2
    (gameF_nonpast_below_next_diagonal_row_present
      hvPos hvBelow hvNonpast)

#print axioms recurrence_nonpast_below_diagonal_strict_prefix
#print axioms recurrence_nonpast_below_next_diagonal_cannot_vanish
#print axioms gameF_nonpast_below_next_diagonal_cannot_vanish

end ChompLean
