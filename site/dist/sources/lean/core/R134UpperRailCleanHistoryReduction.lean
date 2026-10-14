import R132UpperRailOwnerCoverageReduction

set_option autoImplicit false

namespace ChompLean

/-!
Exact relation between the upper-rail `CLEAN` premise, the old
`ColumnNotYetV` coordinate, and R15's `ParkedOnly` predicate.

The key distinction is vertical.  At the lag-three preview row, a preview
host to the left of the candidate puts the target in the current-row prefix,
so `ParkedOnly` is false even if the candidate column already has old target
history.  At the later target row, before the target's freeze, the row-prefix
channel disappears and that same old history is exactly `ParkedOnly`.
-/

/-- Literal all-rows spelling of `ColumnNotYetV` at one column. -/
def ColumnNotYet
    (f : Nat -> Nat -> Nat) (top c z : Nat) : Prop :=
  forall a, c <= a -> a < top -> f a c ≠ z

/-- `CLEAN` is definitionally the one-column `ColumnNotYet` statement. -/
theorem not_colHistPred_iff_columnNotYet
    {f : Nat -> Nat -> Nat} {top c z : Nat} :
    Not (ColHistPred f top c z) <-> ColumnNotYet f top c z := by
  constructor
  · intro hclean a hca hat hvalue
    exact hclean ⟨a, hca, hat, hvalue⟩
  · intro hnotYet hhist
    rcases hhist with ⟨a, hca, hat, hvalue⟩
    exact hnotYet a hca hat hvalue

/-- Column history is monotone in its top-row cutoff.  Once an old
occurrence exists, a later retention/restoration statement cannot erase it. -/
theorem colHistPred_mono_top
    {f : Nat -> Nat -> Nat} {q top c z : Nat}
    (hqt : q <= top) (hhist : ColHistPred f q c z) :
    ColHistPred f top c z := by
  rcases hhist with ⟨a, hca, haq, hvalue⟩
  exact ⟨a, hca, by omega, hvalue⟩

/-- If diagonal-prefix membership is excluded, column history and the
strict old-column tail are the same predicate.  The only apparent extra
case is the diagonal cell `(c,c)`, which the premise removes. -/
theorem colHistPred_iff_colTail_of_no_diagPrefix
    {f : Nat -> Nat -> Nat} {top c z : Nat}
    (hnoDiag : Not (DiagPrefix f top c z)) :
    ColHistPred f top c z <-> ColTail f top c z := by
  constructor
  · rintro ⟨a, hca, hat, hvalue⟩
    by_cases hac : c < a
    · exact ⟨a, hat, hac, hvalue⟩
    · have hacEq : a = c := by omega
      subst a
      exact False.elim (hnoDiag ⟨c, hat, Nat.le_refl c, hvalue⟩)
  · rintro ⟨a, hat, hca, hvalue⟩
    exact ⟨a, Nat.le_of_lt hca, hat, hvalue⟩

/-- Under absence from the diagonal and current-row prefix channels,
`ParkedOnly` is exactly old same-column history. -/
theorem parkedOnly_iff_colHistPred_of_no_diag_no_row
    {f : Nat -> Nat -> Nat} {top c z : Nat}
    (hnoDiag : Not (DiagPrefix f top c z))
    (hnoRow : Not (C f top c z)) :
    ParkedOnly f top c z <-> ColHistPred f top c z := by
  constructor
  · intro hpark
    exact (colHistPred_iff_colTail_of_no_diagPrefix hnoDiag).2 hpark.1
  · intro hhist
    exact ⟨(colHistPred_iff_colTail_of_no_diagPrefix hnoDiag).1 hhist,
      hnoDiag, hnoRow⟩

/-- Before the actual freeze column of a row-start blocker, old column
history is exactly an R15 parked-only occurrence. -/
theorem gameF_parkedOnly_iff_colHistPred_before_freeze
    {v r c : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hcr : c < r) :
    ParkedOnly gameF v c v <-> ColHistPred gameF v c v := by
  have hnoDiag : Not (DiagPrefix gameF v c v) := by
    rintro ⟨a, _hav, _hac, hdiag⟩
    exact disjoint_D_S gameRecurrenceModel
      ⟨a, hdiag⟩ ⟨r, hrv, hstart⟩
  have hnoRow : Not (C gameF v c v) := by
    rintro ⟨b, hbc, hvalue⟩
    have heq := gameRecurrenceModel.fixed_q_injective
      (q := v) (b₁ := b) (b₂ := r)
      (by omega) (by omega) (hvalue.trans hstart.symm)
    omega
  exact parkedOnly_iff_colHistPred_of_no_diag_no_row hnoDiag hnoRow

/-- Negated form used by the upper-rail proof: `CLEAN` is equivalent to the
absence of an R15 parked-only occurrence. -/
theorem gameF_clean_iff_no_parkedOnly_before_freeze
    {v r c : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hcr : c < r) :
    Not (ColHistPred gameF v c v) <->
      Not (ParkedOnly gameF v c v) := by
  exact (not_congr
    (gameF_parkedOnly_iff_colHistPred_before_freeze hrv hstart hcr)).symm

/-- A preview to the left of a candidate masks every old-history occurrence
from the `ParkedOnly` predicate at the preview row, because it enters the
current-row prefix channel. -/
theorem preview_left_not_parkedOnly
    {q previewHost c z : Nat}
    (hhc : previewHost < c)
    (hhost : gameF q previewHost = z) :
    Not (ParkedOnly gameF q c z) := by
  intro hpark
  exact hpark.2.2 ⟨previewHost, hhc, hhost⟩

/-- Exact vertical-unmasking no-go for using R15 alone on the CLEAN debt.
An old occurrence is not parked-only at the preview row (the left preview
masks it), but the same occurrence becomes parked-only at the later target
row as long as that row has not yet reached its freeze column. -/
theorem old_history_unmasks_as_parkedOnly_before_freeze
    {q v r previewHost c : Nat}
    (hqv : q <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hcr : c < r)
    (hhc : previewHost < c)
    (hhost : gameF q previewHost = v)
    (hhist : ColHistPred gameF q c v) :
    Not (ParkedOnly gameF q c v) /\
      ParkedOnly gameF v c v := by
  constructor
  · exact preview_left_not_parkedOnly hhc hhost
  · have hhistFinal := colHistPred_mono_top hqv hhist
    exact (gameF_parkedOnly_iff_colHistPred_before_freeze
      hrv hstart hcr).2 hhistFinal

#print axioms not_colHistPred_iff_columnNotYet
#print axioms colHistPred_mono_top
#print axioms colHistPred_iff_colTail_of_no_diagPrefix
#print axioms parkedOnly_iff_colHistPred_of_no_diag_no_row
#print axioms gameF_parkedOnly_iff_colHistPred_before_freeze
#print axioms gameF_clean_iff_no_parkedOnly_before_freeze
#print axioms preview_left_not_parkedOnly
#print axioms old_history_unmasks_as_parkedOnly_before_freeze

end ChompLean
