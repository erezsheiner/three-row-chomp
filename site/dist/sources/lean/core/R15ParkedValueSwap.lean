import ChompLean.Proof
import Std

set_option autoImplicit false

namespace ChompLean

/-!
R15: exact source algebra for a one-column move.

There is no monotonicity claim for `B f t e`: when `e` is replaced by
`e+1`, the whole tail of the fixed `R`/column-history channel changes.
The definitions below name the three channels so that this change cannot be
silently dropped.
-/

/-- Diagonal values whose owners have already reached column `e`. -/
def DiagPrefix
    (f : Nat -> Nat -> Nat) (t e z : Nat) : Prop :=
  exists a, a < t /\ a <= e /\ f a a = z

/-- The genuinely column-dependent tail of `R f t e`. -/
def ColTail
    (f : Nat -> Nat -> Nat) (t e z : Nat) : Prop :=
  exists a, a < t /\ e < a /\ f a e = z

/-- `z` is present at column `e` only through its column-history tail. -/
def ParkedOnly
    (f : Nat -> Nat -> Nat) (t e z : Nat) : Prop :=
  ColTail f t e z /\ Not (DiagPrefix f t e z) /\ Not (C f t e z)

/-! ## Exact channel expansions -/

theorem R_iff_diagPrefix_or_colTail
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    R f t e z <-> DiagPrefix f t e z \/ ColTail f t e z := by
  constructor
  · rintro ⟨a, hat, hval⟩
    by_cases hae : a <= e
    · left
      refine ⟨a, hat, hae, ?_⟩
      simpa [Nat.min_eq_left hae] using hval
    · right
      have hea : e < a := Nat.lt_of_not_ge hae
      refine ⟨a, hat, hea, ?_⟩
      simpa [Nat.min_eq_right (Nat.le_of_lt hea)] using hval
  · rintro (hdiag | hcol)
    · rcases hdiag with ⟨a, hat, hae, hval⟩
      refine ⟨a, hat, ?_⟩
      simpa [Nat.min_eq_left hae] using hval
    · rcases hcol with ⟨a, hat, hea, hval⟩
      refine ⟨a, hat, ?_⟩
      simpa [Nat.min_eq_right (Nat.le_of_lt hea)] using hval

theorem C_successor
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    C f t (e + 1) z <-> C f t e z \/ f t e = z := by
  constructor
  · rintro ⟨b, hbe, hval⟩
    by_cases hblt : b < e
    · exact Or.inl ⟨b, hblt, hval⟩
    · have hbeq : b = e := by omega
      subst b
      exact Or.inr hval
  · rintro (hold | hfresh)
    · rcases hold with ⟨b, hbe, hval⟩
      exact ⟨b, by omega, hval⟩
    · exact ⟨e, by omega, hfresh⟩

theorem diagPrefix_successor
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    DiagPrefix f t (e + 1) z <->
      DiagPrefix f t e z \/ (e + 1 < t /\ f (e + 1) (e + 1) = z) := by
  constructor
  · rintro ⟨a, hat, hae, hval⟩
    by_cases haold : a <= e
    · exact Or.inl ⟨a, hat, haold, hval⟩
    · have haeq : a = e + 1 := by omega
      subst a
      exact Or.inr ⟨hat, hval⟩
  · rintro (hold | hnew)
    · rcases hold with ⟨a, hat, hae, hval⟩
      exact ⟨a, hat, by omega, hval⟩
    · exact ⟨e + 1, hnew.1, Nat.le_refl _, hnew.2⟩

/--
The exact one-column source expansion.  The `ColTail` term at `e+1` is a
new channel, not a subset of the source at `e` and not implied by a diagonal
or row-prefix occurrence.
-/
theorem B_successor_exact
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    B f t (e + 1) z <->
      DiagPrefix f t (e + 1) z \/
      ColTail f t (e + 1) z \/
      C f t e z \/
      f t e = z := by
  rw [B, R_iff_diagPrefix_or_colTail, C_successor]
  constructor
  · intro h
    rcases h with hR | hC
    · rcases hR with hD | hCol
      · exact Or.inl hD
      · exact Or.inr (Or.inl hCol)
    · rcases hC with hOld | hFresh
      · exact Or.inr (Or.inr (Or.inl hOld))
      · exact Or.inr (Or.inr (Or.inr hFresh))
  · intro h
    rcases h with hD | hCol | hOld | hFresh
    · exact Or.inl (Or.inl hD)
    · exact Or.inl (Or.inr hCol)
    · exact Or.inr (Or.inl hOld)
    · exact Or.inr (Or.inr hFresh)

/-- The same expansion with the newly added diagonal value separated. -/
theorem B_successor_exact_delta
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    B f t (e + 1) z <->
      DiagPrefix f t e z \/
      (e + 1 < t /\ f (e + 1) (e + 1) = z) \/
      ColTail f t (e + 1) z \/
      C f t e z \/
      f t e = z := by
  rw [B_successor_exact, diagPrefix_successor]
  constructor
  · intro h
    rcases h with hD | hCol | hOld | hFresh
    · rcases hD with hOldDiag | hNewDiag
      · exact Or.inl hOldDiag
      · exact Or.inr (Or.inl hNewDiag)
    · exact Or.inr (Or.inr (Or.inl hCol))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hOld)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hFresh)))
  · intro h
    rcases h with hOldDiag | hNewDiag | hCol | hOld | hFresh
    · exact Or.inl (Or.inl hOldDiag)
    · exact Or.inl (Or.inr hNewDiag)
    · exact Or.inr (Or.inl hCol)
    · exact Or.inr (Or.inr (Or.inl hOld))
    · exact Or.inr (Or.inr (Or.inr hFresh))

/-! ## Parked-value swap and fresh closing -/

theorem parkedOnly_mem_current_source
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hpark : ParkedOnly f t e z) :
    B f t e z := by
  left
  exact R_iff_diagPrefix_or_colTail.mpr (Or.inr hpark.1)

/--
Every actual one-step source loss was old-column-only before the move.
Diagonal-prefix and row-prefix membership both persist to the successor.
-/
theorem source_loss_implies_parkedOnly
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hcurrent : B f t e z) (hlost : Not (B f t (e + 1) z)) :
    ParkedOnly f t e z := by
  have hnotDiag : Not (DiagPrefix f t e z) := by
    intro hDiag
    apply hlost
    exact B_successor_exact_delta.mpr (Or.inl hDiag)
  have hnotRow : Not (C f t e z) := by
    intro hRow
    apply hlost
    exact B_successor_exact_delta.mpr
      (Or.inr (Or.inr (Or.inr (Or.inl hRow))))
  have hcol : ColTail f t e z := by
    rcases hcurrent with hR | hC
    · rcases R_iff_diagPrefix_or_colTail.mp hR with hDiag | hCol
      · exact False.elim (hnotDiag hDiag)
      · exact hCol
    · exact False.elim (hnotRow hC)
  exact ⟨hcol, hnotDiag, hnotRow⟩

/--
Exact next-column fate of a parked-only value.  Besides the new diagonal and
the fresh row cell, a new-column-tail occurrence is an independent option.
-/
theorem parked_value_next_source_exact
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hpark : ParkedOnly f t e z) :
    B f t (e + 1) z <->
      (e + 1 < t /\ f (e + 1) (e + 1) = z) \/
      ColTail f t (e + 1) z \/
      f t e = z := by
  rw [B_successor_exact_delta]
  constructor
  · intro h
    rcases h with holdDiag | hnewDiag | hnewCol | holdRow | hfresh
    · exact False.elim (hpark.2.1 holdDiag)
    · exact Or.inl hnewDiag
    · exact Or.inr (Or.inl hnewCol)
    · exact False.elim (hpark.2.2 holdRow)
    · exact Or.inr (Or.inr hfresh)
  · intro h
    rcases h with hnewDiag | hnewCol | hfresh
    · exact Or.inr (Or.inl hnewDiag)
    · exact Or.inr (Or.inr (Or.inl hnewCol))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hfresh)))

/-- Correct swap-out criterion, with every possible replacement channel. -/
theorem parked_value_swaps_out
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hpark : ParkedOnly f t e z)
    (hnewDiag : Not (e + 1 < t /\ f (e + 1) (e + 1) = z))
    (hnewCol : Not (ColTail f t (e + 1) z))
    (hfresh : Not (f t e = z)) :
    B f t e z /\ Not (B f t (e + 1) z) := by
  constructor
  · exact parkedOnly_mem_current_source hpark
  · intro hnext
    rcases (parked_value_next_source_exact hpark).mp hnext with hD | hCol | hF
    · exact hnewDiag hD
    · exact hnewCol hCol
    · exact hfresh hF

/-- Exact normal form of a one-column source loss. -/
theorem source_loss_iff_parked_and_no_replacement
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    (B f t e z /\ Not (B f t (e + 1) z)) <->
      (ParkedOnly f t e z /\
       Not (e + 1 < t /\ f (e + 1) (e + 1) = z) /\
       Not (ColTail f t (e + 1) z) /\
       Not (f t e = z)) := by
  constructor
  · rintro ⟨hcurrent, hlost⟩
    have hpark := source_loss_implies_parkedOnly hcurrent hlost
    have hfate := parked_value_next_source_exact hpark
    refine ⟨hpark, ?_, ?_, ?_⟩
    · intro hD
      exact hlost (hfate.mpr (Or.inl hD))
    · intro hCol
      exact hlost (hfate.mpr (Or.inr (Or.inl hCol)))
    · intro hFresh
      exact hlost (hfate.mpr (Or.inr (Or.inr hFresh)))
  · rintro ⟨hpark, hD, hCol, hFresh⟩
    exact parked_value_swaps_out hpark hD hCol hFresh

/-- A fresh emission closes its value at the very next column. -/
theorem fresh_emission_closes_next
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hfresh : f t e = z) :
    B f t (e + 1) z := by
  right
  exact ⟨e, by omega, hfresh⟩

/-- The closing is permanent in the fixed row-prefix channel. -/
theorem fresh_emission_persists_in_row_prefix
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hfresh : f t e = z) :
    forall {r}, e < r -> C f t r z := by
  intro r her
  exact ⟨e, her, hfresh⟩

/-- Hence every later source in that row contains the freshly emitted value. -/
theorem fresh_emission_persists_in_all_later_sources
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hfresh : f t e = z) :
    forall {r}, e < r -> B f t r z := by
  intro r her
  exact Or.inr (fresh_emission_persists_in_row_prefix hfresh her)

/-! ## Counterframe to the proposed two-channel implication -/

def parkedSwapCounter (a b : Nat) : Nat :=
  if a = 2 /\ b = 1 then 7
  else if a = 3 /\ b = 2 then 7
  else 0

theorem parkedSwapCounter_parked_only :
    ParkedOnly parkedSwapCounter 4 1 7 := by
  constructor
  · exact ⟨2, by omega, by omega, by simp [parkedSwapCounter]⟩
  constructor
  · rintro ⟨a, ha4, ha1, hval⟩
    unfold parkedSwapCounter at hval
    split at hval
    · rename_i hbad
      omega
    · split at hval
      · rename_i hbad
        omega
      · omega
  · rintro ⟨b, hb1, hval⟩
    simp [parkedSwapCounter] at hval

theorem parkedSwapCounter_next_new_col :
    ColTail parkedSwapCounter 4 2 7 := by
  exact ⟨3, by omega, by omega, by simp [parkedSwapCounter]⟩

theorem parkedSwapCounter_next_no_diag :
    Not (DiagPrefix parkedSwapCounter 4 2 7) := by
  rintro ⟨a, ha4, ha2, hval⟩
  unfold parkedSwapCounter at hval
  split at hval
  · rename_i hbad
    omega
  · split at hval
    · rename_i hbad
      omega
    · omega

theorem parkedSwapCounter_next_no_row :
    Not (C parkedSwapCounter 4 2 7) := by
  rintro ⟨b, hb2, hval⟩
  simp [parkedSwapCounter] at hval

/--
The omitted-new-column formulation is false: this value is parked only at
column 1 and is still in the source at column 2, although it is in neither
the diagonal prefix nor the row prefix there.  It survives via `ColTail 2`.
-/
theorem omitted_new_column_channel_counterframe :
    ParkedOnly parkedSwapCounter 4 1 7 /\
    B parkedSwapCounter 4 2 7 /\
    Not (DiagPrefix parkedSwapCounter 4 2 7) /\
    Not (C parkedSwapCounter 4 2 7) := by
  refine ⟨parkedSwapCounter_parked_only, ?_,
    parkedSwapCounter_next_no_diag, parkedSwapCounter_next_no_row⟩
  left
  exact R_iff_diagPrefix_or_colTail.mpr
    (Or.inr parkedSwapCounter_next_new_col)

end ChompLean
