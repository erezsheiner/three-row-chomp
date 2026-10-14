import R55Integration

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
R56: generic V-catch gate and exact column-age sentinels.

`PastHostColumn M q u b` records a genuine earlier, non-diagonal host of
`u` in column `b`: its row lies strictly between the birth row `b` of the
column and the current row `q`.  This is exactly the witness returned by
the R55 left-history law.

The column-age part below is purely triangular arithmetic.  Before row
`t+1`, column `t-1` has only its diagonal cell and the V1 cell in row `t`;
column `t-2` has only its diagonal cell, the V1 cell in row `t-1`, and the
V2 cell in row `t`.  The final theorem composes those exact histories with
the gate: a high non-past value caught in column `t` or `t+1`, but absent
from those five recent cells, forces both preceding edge cells below it.
-/

/-- Column `b` hosted `u` after the column was born and before row `q`. -/
def PastHostColumn (M : RecurrenceModel) (q u b : Nat) : Prop :=
  exists a, b < a /\ a < q /\ M.f a b = u

/-- The inclusive history of column `b` before row `q`, including its
diagonal birth cell. -/
def ColumnHistoryValue (M : RecurrenceModel) (q u b : Nat) : Prop :=
  exists a, b <= a /\ a < q /\ M.f a b = u

/-- A value is outside the five cells comprising the complete histories
of columns `t-1` and `t-2` before row `t+1` (when `2 <= t`). -/
def DeepBeyondLastTwoColumnHistories
    (M : RecurrenceModel) (t u : Nat) : Prop :=
  u ≠ M.f (t - 1) (t - 1) /\
  u ≠ M.f t (t - 1) /\
  u ≠ M.f (t - 2) (t - 2) /\
  u ≠ M.f (t - 1) (t - 2) /\
  u ≠ M.f t (t - 2)

/-- Row-weak LEFT-HISTORY.  The caught value may equal the current row;
the strictly larger cell is still live, which is all `mex_no_skip` needs. -/
theorem left_history_of_higher_left_column_of_row_le
    (M : RecurrenceModel) {q u c b : Nat}
    (hcq : c <= q) (hbc : b < c) (hqu : q <= u)
    (hhost : M.f q c = u) (hhigher : u < M.f q b)
    (hnotPast : forall a, a < q -> M.f a a ≠ u) :
    exists a, b < a /\ a < q /\ M.f a b = u := by
  have huPos : 0 < u := by
    have hindex := M.value_gt_index hcq
    rw [hhost] at hindex
    omega
  have hB : B M.f q b u := by
    apply M.mex_no_skip (by omega)
    · omega
    · exact huPos
    · exact hhigher
  rcases hB with hR | hC
  · rcases hR with ⟨a, haq, hvalue⟩
    by_cases hab : a <= b
    · have hmin : min a b = a := Nat.min_eq_left hab
      rw [hmin] at hvalue
      exact False.elim ((hnotPast a haq) hvalue)
    · have hba : b < a := by omega
      have hmin : min a b = b := Nat.min_eq_right (by omega)
      rw [hmin] at hvalue
      exact ⟨a, hba, haq, hvalue⟩
  · rcases hC with ⟨r, hrb, hvalue⟩
    have hrc : r = c :=
      M.fixed_q_injective (by omega) hcq
        (hvalue.trans hhost.symm)
    omega

/-- Generic V-catch gate.  Every larger value strictly left of the current
host of a row-high-or-equal non-past value certifies a strict prior host in
that column. -/
theorem vCatch_gate
    (M : RecurrenceModel) {q u c : Nat}
    (hcq : c <= q) (hqu : q <= u)
    (hhost : M.f q c = u)
    (hnotPast : forall a, a < q -> M.f a a ≠ u) :
    forall b, b < c -> u < M.f q b -> PastHostColumn M q u b := by
  intro b hbc hhigher
  exact left_history_of_higher_left_column_of_row_le M hcq hbc hqu hhost
    hhigher hnotPast

/-- Pointwise gate form, useful when the column is already fixed. -/
theorem pastHostColumn_of_vCatch_higher
    (M : RecurrenceModel) {q u c b : Nat}
    (hcq : c <= q) (hbc : b < c) (hqu : q <= u)
    (hhost : M.f q c = u) (hhigher : u < M.f q b)
    (hnotPast : forall a, a < q -> M.f a a ≠ u) :
    PastHostColumn M q u b :=
  vCatch_gate M hcq hqu hhost hnotPast b hbc hhigher

/-- If a column left of the catch host has no prior host witness, its
current value is strictly below the caught value.  Row injectivity rules
out equality, while `vCatch_gate` rules out a larger value. -/
theorem vCatch_below_of_not_pastHostColumn
    (M : RecurrenceModel) {q u c b : Nat}
    (hcq : c <= q) (hbc : b < c) (hqu : q <= u)
    (hhost : M.f q c = u)
    (hnotPast : forall a, a < q -> M.f a a ≠ u)
    (hnoHost : Not (PastHostColumn M q u b)) :
    M.f q b < u := by
  have hnotHigher : Not (u < M.f q b) := by
    intro hhigher
    exact hnoHost
      (pastHostColumn_of_vCatch_higher M hcq hbc hqu hhost
        hhigher hnotPast)
  have hne : M.f q b ≠ u := by
    intro heq
    have hbcEq : b = c :=
      M.fixed_q_injective (by omega) hcq (heq.trans hhost.symm)
    omega
  omega

/-- V1-host specialization at row `t+1`: every higher strict-prefix
column is a past host column. -/
theorem vCatch_gate_at_V1_host
    (M : RecurrenceModel) {t u : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u) :
    forall b, b < t -> u < M.f (t + 1) b ->
      PastHostColumn M (t + 1) u b := by
  have hqu : t + 1 <= u := by
    have hindex := M.value_gt_index (q := t + 1) (r := t) (by omega)
    rw [hhost] at hindex
    omega
  exact vCatch_gate M (by omega) hqu hhost hnotPast

/-- A newly caught diagonal value automatically satisfies the non-past
condition, by diagonal injectivity, so its gate needs no extra hypothesis. -/
theorem diagonal_vCatch_gate
    (M : RecurrenceModel) {q b : Nat}
    (hbq : b < q) (hhigher : M.f q q < M.f q b) :
    PastHostColumn M q (M.f q q) b := by
  apply pastHostColumn_of_vCatch_higher M (c := q)
      (Nat.le_refl q) hbq (Nat.le_of_lt (M.diagonal_gt q)) rfl hhigher
  intro a haq hEq
  have haqEq : a = q := diagonal_injective M hEq
  omega

/-- Exact inclusive history of column `t-1` before row `t+1`. -/
theorem column_t_sub_one_history_exact
    (M : RecurrenceModel) {t u : Nat} (ht : 1 <= t) :
    ColumnHistoryValue M (t + 1) u (t - 1) <->
      M.f (t - 1) (t - 1) = u \/ M.f t (t - 1) = u := by
  constructor
  · rintro ⟨a, hlow, hhigh, hvalue⟩
    have ha : a = t - 1 \/ a = t := by omega
    rcases ha with ha | ha
    · subst a
      exact Or.inl hvalue
    · subst a
      exact Or.inr hvalue
  · intro h
    rcases h with hdiag | hV1
    · exact ⟨t - 1, Nat.le_refl _, by omega, hdiag⟩
    · exact ⟨t, by omega, by omega, hV1⟩

/-- Exact inclusive history of column `t-2` before row `t+1`. -/
theorem column_t_sub_two_history_exact
    (M : RecurrenceModel) {t u : Nat} (ht : 2 <= t) :
    ColumnHistoryValue M (t + 1) u (t - 2) <->
      M.f (t - 2) (t - 2) = u \/
      M.f (t - 1) (t - 2) = u \/
      M.f t (t - 2) = u := by
  constructor
  · rintro ⟨a, hlow, hhigh, hvalue⟩
    have ha : a = t - 2 \/ a = t - 1 \/ a = t := by omega
    rcases ha with ha | ha | ha
    · subst a
      exact Or.inl hvalue
    · subst a
      exact Or.inr (Or.inl hvalue)
    · subst a
      exact Or.inr (Or.inr hvalue)
  · intro h
    rcases h with hdiag | hV1 | hV2
    · exact ⟨t - 2, Nat.le_refl _, by omega, hdiag⟩
    · exact ⟨t - 1, by omega, by omega, hV1⟩
    · exact ⟨t, by omega, by omega, hV2⟩

/-- Exact strict past-host history of column `t-1`: after excluding its
diagonal birth row, only the V1 cell in row `t` remains. -/
theorem pastHostColumn_t_sub_one_exact
    (M : RecurrenceModel) {t u : Nat} (ht : 1 <= t) :
    PastHostColumn M (t + 1) u (t - 1) <->
      M.f t (t - 1) = u := by
  constructor
  · rintro ⟨a, hlow, hhigh, hvalue⟩
    have ha : a = t := by omega
    subst a
    exact hvalue
  · intro hV1
    exact ⟨t, by omega, by omega, hV1⟩

/-- Exact strict past-host history of column `t-2`: only V1 in row
`t-1` and V2 in row `t` remain after the diagonal birth row. -/
theorem pastHostColumn_t_sub_two_exact
    (M : RecurrenceModel) {t u : Nat} (ht : 2 <= t) :
    PastHostColumn M (t + 1) u (t - 2) <->
      M.f (t - 1) (t - 2) = u \/ M.f t (t - 2) = u := by
  constructor
  · rintro ⟨a, hlow, hhigh, hvalue⟩
    have ha : a = t - 1 \/ a = t := by omega
    rcases ha with ha | ha
    · subst a
      exact Or.inl hvalue
    · subst a
      exact Or.inr hvalue
  · intro h
    rcases h with hV1 | hV2
    · exact ⟨t - 1, by omega, by omega, hV1⟩
    · exact ⟨t, by omega, by omega, hV2⟩

/-- A deep value is absent from the complete pre-`t+1` history of
column `t-1`. -/
theorem deep_not_columnHistory_t_sub_one
    (M : RecurrenceModel) {t u : Nat} (ht : 2 <= t)
    (hdeep : DeepBeyondLastTwoColumnHistories M t u) :
    Not (ColumnHistoryValue M (t + 1) u (t - 1)) := by
  intro hhistory
  rcases (column_t_sub_one_history_exact M (by omega)).mp hhistory with
    hdiag | hV1
  · exact hdeep.1 hdiag.symm
  · exact hdeep.2.1 hV1.symm

/-- A deep value is absent from the complete pre-`t+1` history of
column `t-2`. -/
theorem deep_not_columnHistory_t_sub_two
    (M : RecurrenceModel) {t u : Nat} (ht : 2 <= t)
    (hdeep : DeepBeyondLastTwoColumnHistories M t u) :
    Not (ColumnHistoryValue M (t + 1) u (t - 2)) := by
  intro hhistory
  rcases (column_t_sub_two_history_exact M ht).mp hhistory with
    hdiag | hV1 | hV2
  · exact hdeep.2.2.1 hdiag.symm
  · exact hdeep.2.2.2.1 hV1.symm
  · exact hdeep.2.2.2.2 hV2.symm

/-- In particular, deep values have no strict prior host in either of
the two preceding edge columns. -/
theorem deep_not_pastHostColumn_last_two
    (M : RecurrenceModel) {t u : Nat} (ht : 2 <= t)
    (hdeep : DeepBeyondLastTwoColumnHistories M t u) :
    Not (PastHostColumn M (t + 1) u (t - 1)) /\
    Not (PastHostColumn M (t + 1) u (t - 2)) := by
  constructor
  · intro hpast
    apply deep_not_columnHistory_t_sub_one M ht hdeep
    rcases hpast with ⟨a, hlow, hhigh, hvalue⟩
    exact ⟨a, Nat.le_of_lt hlow, hhigh, hvalue⟩
  · intro hpast
    apply deep_not_columnHistory_t_sub_two M ht hdeep
    rcases hpast with ⟨a, hlow, hhigh, hvalue⟩
    exact ⟨a, Nat.le_of_lt hlow, hhigh, hvalue⟩

/-- COLUMN-AGE SENTINEL.  Let a high non-past value be caught at row
`t+1` in either column `t` or column `t+1` (more generally, any `c` in
that interval).  If it is outside the exact five-cell histories of the
preceding two columns, both current edge occupants are strictly below it. -/
theorem vCatch_last_two_columns_below
    (M : RecurrenceModel) {t u c : Nat}
    (ht : 2 <= t) (htc : t <= c) (hcq : c <= t + 1)
    (hhost : M.f (t + 1) c = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u)
    (hdeep : DeepBeyondLastTwoColumnHistories M t u) :
    M.f (t + 1) (t - 1) < u /\
    M.f (t + 1) (t - 2) < u := by
  have hno := deep_not_pastHostColumn_last_two M ht hdeep
  have hqu : t + 1 <= u := by
    have hindex := M.value_gt_index hcq
    rw [hhost] at hindex
    omega
  constructor
  · exact vCatch_below_of_not_pastHostColumn M hcq (by omega)
      hqu hhost hnotPast hno.1
  · exact vCatch_below_of_not_pastHostColumn M hcq (by omega)
      hqu hhost hnotPast hno.2

/-- Direct V1 specialization of the column-age sentinel. -/
theorem vCatch_at_V1_last_two_columns_below
    (M : RecurrenceModel) {t u : Nat}
    (ht : 2 <= t)
    (hhost : M.f (t + 1) t = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u)
    (hdeep : DeepBeyondLastTwoColumnHistories M t u) :
    M.f (t + 1) (t - 1) < u /\
    M.f (t + 1) (t - 2) < u := by
  exact vCatch_last_two_columns_below M ht (c := t)
    (Nat.le_refl t) (Nat.le_succ t) hhost hnotPast hdeep

/-- Diagonal specialization of the column-age sentinel.  Highness and
non-pastness are automatic for a diagonal catch. -/
theorem diagonal_vCatch_last_two_columns_below
    (M : RecurrenceModel) {t : Nat} (ht : 2 <= t)
    (hdeep : DeepBeyondLastTwoColumnHistories
      M t (M.f (t + 1) (t + 1))) :
    M.f (t + 1) (t - 1) < M.f (t + 1) (t + 1) /\
    M.f (t + 1) (t - 2) < M.f (t + 1) (t + 1) := by
  apply vCatch_last_two_columns_below M ht (c := t + 1)
      (Nat.le_succ t) (Nat.le_refl _) rfl
  · intro a ha hEq
    have haEq : a = t + 1 := diagonal_injective M hEq
    omega
  · exact hdeep

#print axioms vCatch_gate
#print axioms left_history_of_higher_left_column_of_row_le
#print axioms vCatch_below_of_not_pastHostColumn
#print axioms column_t_sub_one_history_exact
#print axioms column_t_sub_two_history_exact
#print axioms vCatch_last_two_columns_below
#print axioms vCatch_at_V1_last_two_columns_below
#print axioms diagonal_vCatch_last_two_columns_below

end ChompLean
