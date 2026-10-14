import R29TerminalBlockerMexCompletion

set_option autoImplicit false

namespace ChompLean

/-!
R30: order of a current-row service column relative to its row-start freeze.

Suppose `f z r = z`, with `r < z`, and row `t <= z` contains `z` at a
column `b < t`.  There are exactly two chronological possibilities.

* Before the row start (`t < z`), `rowStartPropagation` supplies a copy of
  `z` strictly to the left of `r`.  Fixed-row injectivity identifies that
  copy with the given host, so `b < r`.
* On the row start itself (`t = z`), fixed-row injectivity identifies the
  host with the row-start column, so `b = r`.

The last theorem adds this exact order information to R29's terminal MEX
completion package.
-/

/-- Exact order law for a host observed no later than its row start. -/
theorem rowstart_host_order_exact
    (M : RecurrenceModel) {z r t b : Nat}
    (hrz : r < z) (hstart : M.f z r = z)
    (hbt : b < t) (htz : t <= z) (hhost : M.f t b = z) :
    (t < z /\ b < r) \/ (t = z /\ b = r) := by
  by_cases htStrict : t < z
  · left
    refine ⟨htStrict, ?_⟩
    by_cases hrt : r < t
    · rcases rowStartPropagation M hstart hrz hrt htStrict with
        ⟨b', hb'r, hb'host⟩
      have hbb' : b = b' :=
        M.fixed_q_injective (Nat.le_of_lt hbt) (by omega)
          (hhost.trans hb'host.symm)
      omega
    · omega
  · have htzEq : t = z := by omega
    subst t
    right
    refine ⟨rfl, ?_⟩
    exact M.fixed_q_injective (Nat.le_of_lt hbt) (Nat.le_of_lt hrz)
      (hhost.trans hstart.symm)

/-- Weaker disjunctive form convenient when only the column inequality is
needed.  Equality with the freeze is possible only on the boundary row
`t=z`. -/
theorem rowstart_host_before_freeze_or_boundary
    (M : RecurrenceModel) {z r t b : Nat}
    (hrz : r < z) (hstart : M.f z r = z)
    (hbt : b < t) (htz : t <= z) (hhost : M.f t b = z) :
    b < r \/ (z = t /\ b = r) := by
  rcases rowstart_host_order_exact M hrz hstart hbt htz hhost with
    ⟨_, hbr⟩ | ⟨htzEq, hbr⟩
  · exact Or.inl hbr
  · exact Or.inr ⟨htzEq.symm, hbr⟩

/-- In the `L=3` geometry the boundary case pins both the terminal host and
the freeze to the same one of the three terminal columns.  Strictly before
the row start, the terminal host lies strictly to the left of the freeze. -/
theorem l3_terminal_host_column_vs_freeze
    (M : RecurrenceModel) {e z r b : Nat}
    (hb : b = e + 3 \/ b = e + 4 \/ b = e + 5)
    (hrz : r < z) (hstart : M.f z r = z)
    (htz : e + 6 <= z) (hhost : M.f (e + 6) b = z) :
    (e + 6 < z /\ b < r) \/
      (z = e + 6 /\
        ((b = e + 3 /\ r = e + 3) \/
         (b = e + 4 /\ r = e + 4) \/
         (b = e + 5 /\ r = e + 5))) := by
  have hbt : b < e + 6 := by
    rcases hb with rfl | rfl | rfl <;> omega
  rcases rowstart_host_order_exact M hrz hstart hbt htz hhost with
    ⟨htStrict, hbr⟩ | ⟨htEq, hbr⟩
  · exact Or.inl ⟨htStrict, hbr⟩
  · right
    refine ⟨htEq.symm, ?_⟩
    rcases hb with hb | hb | hb
    · exact Or.inl ⟨hb, hbr.symm.trans hb⟩
    · exact Or.inr (Or.inl ⟨hb, hbr.symm.trans hb⟩)
    · exact Or.inr (Or.inr ⟨hb, hbr.symm.trans hb⟩)

/-- R29 with the exact service/freeze order retained.  Thus a terminal MEX
service is either strictly left of a genuinely future freeze, or, only when
`z=e+6`, it occurs exactly at the freeze column in the terminal triple. -/
theorem gameF_rm2_missing_l3_backstop_late_blocker_has_ordered_terminal_mex
    {e u z r : Nat}
    (huSeat : gameF (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < gameF (e + 4) (e + 4))
    (hzu : z < u)
    (hrLower : e + 3 <= r) (hrz : r < z)
    (hstart : gameF z r = z)
    (hmissing : Not (B gameF (e + 6) (e + 3) z))
    (hRM2 : TwoStepDiagonalRecordLaw gameRecurrenceModel) :
    exists b,
      (b = e + 3 \/ b = e + 4 \/ b = e + 5) /\
      gameF (e + 6) b = z /\
      IsMex (B gameF (e + 6) b) z /\
      (forall v, 0 < v -> v < z -> B gameF (e + 6) b v) /\
      ((e + 6 < z /\ b < r) \/
        (z = e + 6 /\
          ((b = e + 3 /\ r = e + 3) \/
           (b = e + 4 /\ r = e + 4) \/
           (b = e + 5 /\ r = e + 5)))) := by
  rcases gameF_rm2_missing_l3_backstop_late_blocker_has_terminal_mex
      huSeat hPrevDiagonalAbove hzu hrLower hrz hstart hmissing hRM2 with
    ⟨b, hb, hhost, hmex⟩
  have htz : e + 6 <= z :=
    missing_l3_backstop_late_rowstart_is_at_least_current_row
      gameRecurrenceModel huSeat hzu hrLower hrz hstart hmissing
  have horder :=
    l3_terminal_host_column_vs_freeze gameRecurrenceModel hb hrz hstart
      htz hhost
  exact ⟨b, hb, hhost, hmex, hmex.2.2, horder⟩

end ChompLean
