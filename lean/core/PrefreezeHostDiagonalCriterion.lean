import R26ActualGameFutureGap

set_option autoImplicit false

namespace ChompLean

/-!
The exact recurrence-level content of "pre-freeze hosting".

For a row-start value `z` (a blocker), occurrence on row `q` is equivalent
to the single diagonal inequality `z <= f q q`.  Thus a host can disappear
between consecutive rows only when the diagonal crosses strictly down through
`z`.  The final lemmas record the extra actual-encoding fact that a surviving
host cannot remain in the same column.
-/

/-- A row-start value occurs in the strict prefix of row `q` exactly when it
is at most the diagonal maximum of that row.

The reverse implication is the diagonal MEX-cover argument.  The value is
strictly below the diagonal because diagonal values and row starts are
disjoint; after `mex_no_skip` puts it in `B(q,q)`, the historical-diagonal
branch is excluded by the same disjointness theorem. -/
theorem rowstart_hosted_iff_below_diagonal
    (M : RecurrenceModel) {z r q : Nat}
    (hrz : r < z) (hstart : M.f z r = z) :
    C M.f q q z <-> z <= M.f q q := by
  constructor
  · rintro ⟨b, hbq, hhost⟩
    have hmax := diagonalMaximal M (Nat.le_of_lt hbq)
    rw [hhost] at hmax
    exact hmax
  · intro hzle
    have hdiagNe : M.f q q ≠ z := by
      intro hdiag
      exact disjoint_D_S M ⟨q, hdiag⟩ ⟨r, hrz, hstart⟩
    have hzlt : z < M.f q q := by omega
    have hzpos : 0 < z := by omega
    have hB : B M.f q q z :=
      M.mex_no_skip (Nat.le_refl q) (M.diagonal_gt q) hzpos hzlt
    rcases hB with hR | hC
    · rcases hR with ⟨a, haq, hvalue⟩
      have hmin : min a q = a := Nat.min_eq_left (Nat.le_of_lt haq)
      rw [hmin] at hvalue
      exact False.elim
        (disjoint_D_S M ⟨a, hvalue⟩ ⟨r, hrz, hstart⟩)
    · exact hC

/-- Exact complementary form: a blocker is absent from the strict row prefix
if and only if it lies strictly above that row's diagonal. -/
theorem rowstart_missing_iff_above_diagonal
    (M : RecurrenceModel) {z r q : Nat}
    (hrz : r < z) (hstart : M.f z r = z) :
    Not (C M.f q q z) <-> M.f q q < z := by
  rw [rowstart_hosted_iff_below_diagonal M hrz hstart]
  omega

/-- A historical host lost on the next row forces an exact one-step diagonal
downcross.  This is the honest residue of next-row pre-freeze propagation. -/
theorem prefreeze_host_loss_forces_diagonal_downcross
    (M : RecurrenceModel) {z r a b : Nat}
    (hba : b <= a)
    (hrz : r < z) (hstart : M.f z r = z)
    (hhost : M.f a b = z)
    (hnextMissing : Not (C M.f (a + 1) (a + 1) z)) :
    M.f (a + 1) (a + 1) < z /\ z <= M.f a a := by
  have hdown : M.f (a + 1) (a + 1) < z :=
    (rowstart_missing_iff_above_diagonal M hrz hstart).mp hnextMissing
  have hold := diagonalMaximal M hba
  rw [hhost] at hold
  exact ⟨hdown, hold⟩

/-- Conversely, a strict diagonal downcross is already enough to rule out a
next-row host.  Hence next-row blocker propagation is precisely a diagonal
floor/no-downcross assertion. -/
theorem prefreeze_next_host_iff_no_diagonal_downcross
    (M : RecurrenceModel) {z r a : Nat}
    (hrz : r < z) (hstart : M.f z r = z) :
    C M.f (a + 1) (a + 1) z <-> z <= M.f (a + 1) (a + 1) :=
  rowstart_hosted_iff_below_diagonal M hrz hstart

/-- If a value in the new row is also named, a missing blocker traps the
new diagonal between that value and the lost blocker, while the old diagonal
remains at or above the blocker.  This is the form used by an R21 lower-loss
`q = f(t,e+2)`. -/
theorem prefreeze_host_loss_traps_new_row_value
    (M : RecurrenceModel) {z r a b c : Nat}
    (hba : b <= a) (hc : c <= a + 1)
    (hrz : r < z) (hstart : M.f z r = z)
    (hhost : M.f a b = z)
    (hnextMissing : Not (C M.f (a + 1) (a + 1) z)) :
    M.f (a + 1) c <= M.f (a + 1) (a + 1) /\
      M.f (a + 1) (a + 1) < z /\ z <= M.f a a := by
  have hmax := diagonalMaximal M hc
  have hcross := prefreeze_host_loss_forces_diagonal_downcross
    M hba hrz hstart hhost hnextMissing
  exact ⟨hmax, hcross⟩

/-- In the length-three rescue geometry, `RM2` lifts the old diagonal above
`u` to the current-row diagonal.  Hence every sub-`u` blocker is hosted
somewhere on the current row `e+6`. -/
theorem rm2_sub_u_rowstart_hosted_on_l3_current_row
    (M : RecurrenceModel) {e u z r : Nat}
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hzu : z < u)
    (hrz : r < z) (hstart : M.f z r = z)
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    C M.f (e + 6) (e + 6) z := by
  have hrecord : M.f (e + 4) (e + 4) < M.f (e + 6) (e + 6) :=
    hRM2 (by omega)
  have hfloor : z <= M.f (e + 6) (e + 6) := by omega
  exact (rowstart_hosted_iff_below_diagonal M hrz hstart).2 hfloor

/-- If that blocker is still absent from the length-three backstop source,
its unique current-row host is forced into the three unscanned terminal
cells `e+3,e+4,e+5`. -/
theorem rm2_missing_l3_backstop_rowstart_has_terminal_host
    (M : RecurrenceModel) {e u z r : Nat}
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hzu : z < u)
    (hrz : r < z) (hstart : M.f z r = z)
    (hRM2 : TwoStepDiagonalRecordLaw M)
    (hmissing : Not (B M.f (e + 6) (e + 3) z)) :
    exists b,
      (b = e + 3 \/ b = e + 4 \/ b = e + 5) /\
      M.f (e + 6) b = z := by
  rcases rm2_sub_u_rowstart_hosted_on_l3_current_row
      M hPrevDiagonalAbove hzu hrz hstart hRM2 with
    ⟨b, hbTop, hvalue⟩
  have hbBottom : e + 3 <= b := by
    by_cases hlt : b < e + 3
    · exact False.elim (hmissing (Or.inr ⟨b, hlt, hvalue⟩))
    · omega
  have hcases : b = e + 3 \/ b = e + 4 \/ b = e + 5 := by omega
  exact ⟨b, hcases, hvalue⟩

/-- Encoding-level geometry: a host strictly before a blocker's freeze is
off the diagonal, and it cannot survive in the same column on the next row. -/
theorem encoding_prefreeze_host_must_move_column
    {f : Nat -> Nat -> Nat} (hf : Encodes f)
    {z r a b : Nat}
    (hba : b <= a) (har : a < r)
    (hrz : r < z) (hstart : f z r = z)
    (hhost : f a b = z) :
    b < a /\ f (a + 1) b ≠ z := by
  have hbaStrict : b < a := by
    by_cases hbaEq : b = a
    · subst b
      exact False.elim
        (encoding_rowstart_diagonal_attack hf hstart hrz hhost (by omega))
    · omega
  have hnextNe : f (a + 1) b ≠ z := by
    intro hnext
    exact encoding_same_lower_no_repeat hf
      hbaStrict (by omega) (by omega) hhost hnext
  exact ⟨hbaStrict, hnextNe⟩

/-- Actual-game specialization: if the diagonal floor keeps a pre-freeze
blocker alive, its next-row host exists uniquely and is in a new column. -/
theorem gameF_prefreeze_next_host_unique_and_moved
    {z r a b : Nat}
    (hba : b <= a) (har : a < r)
    (hrz : r < z) (hstart : gameF z r = z)
    (hhost : gameF a b = z)
    (hfloor : z <= gameF (a + 1) (a + 1)) :
    exists b',
      (b' < a + 1 /\ b' ≠ b /\ gameF (a + 1) b' = z) /\
      forall c,
        c < a + 1 /\ c ≠ b /\ gameF (a + 1) c = z -> c = b' := by
  have hC : C gameF (a + 1) (a + 1) z := by
    exact (rowstart_hosted_iff_below_diagonal
      gameRecurrenceModel hrz hstart).2 hfloor
  rcases hC with ⟨b', hb', hvalue⟩
  have hsameNe :=
    (encoding_prefreeze_host_must_move_column
      game_encodes hba har hrz hstart hhost).2
  have hb'Ne : b' ≠ b := by
    intro heq
    subst b'
    exact hsameNe hvalue
  refine ⟨b', ⟨⟨hb', hb'Ne, hvalue⟩, ?_⟩⟩
  intro c hc'
  exact encoding_fixed_q_injective game_encodes
    (Nat.le_of_lt hc'.1) (Nat.le_of_lt hb')
    (hc'.2.2.trans hvalue.symm)

end ChompLean
