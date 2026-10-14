import CeilingTopTwoMexAudit

set_option autoImplicit false

namespace ChompLean

/-!
R56: the exact two-edge source and its first two positive holes.

For a positive row `q`, `TwoEdgeSigma f q` contains all earlier diagonal
values and the current-row columns strictly left of `q - 1`.  Thus it omits
exactly the V1 column `q - 1` and the diagonal column `q` from the current
row.  The source of V1 is exactly this predicate, while the diagonal source
is obtained by adjoining the V1 value.
-/

/-- Past diagonals together with the current row strictly left of V1. -/
def TwoEdgeSigma (f : Nat -> Nat -> Nat) (q v : Nat) : Prop :=
  (exists a, a < q /\ f a a = v) \/
  (exists b, b + 1 < q /\ f q b = v)

/-- `m` is the least positive value outside `S`. -/
def IsFirstPositiveHole (S : Nat -> Prop) (m : Nat) : Prop :=
  IsMex S m

/-- `m1,m2` are the first two positive holes of `S`, in that order.

Equivalently, `m1` is the first positive hole of `S`, and `m2` is the
first positive hole after `m1` has been adjoined to `S`.
-/
def IsFirstTwoPositiveHoles
    (S : Nat -> Prop) (m1 m2 : Nat) : Prop :=
  IsFirstPositiveHole S m1 /\
  IsFirstPositiveHole (fun v => S v \/ v = m1) m2

/-- At a positive row, the V1 source is exactly `TwoEdgeSigma`. -/
theorem B_v1_iff_twoEdgeSigma
    {f : Nat -> Nat -> Nat} {q v : Nat} (hq : 0 < q) :
    B f q (q - 1) v <-> TwoEdgeSigma f q v := by
  constructor
  · intro hv
    rcases hv with hR | hC
    · rcases hR with ⟨a, haq, hvalue⟩
      have hale : a <= q - 1 := by omega
      exact Or.inl ⟨a, haq, by simpa [Nat.min_eq_left hale] using hvalue⟩
    · rcases hC with ⟨b, hb, hvalue⟩
      exact Or.inr ⟨b, by omega, hvalue⟩
  · intro hv
    rcases hv with hdiag | hprefix
    · rcases hdiag with ⟨a, haq, hvalue⟩
      have hale : a <= q - 1 := by omega
      exact Or.inl ⟨a, haq, by simpa [Nat.min_eq_left hale] using hvalue⟩
    · rcases hprefix with ⟨b, hbq, hvalue⟩
      exact Or.inr ⟨b, by omega, hvalue⟩

/-- The diagonal source is `TwoEdgeSigma` with the V1 value adjoined. -/
theorem B_diagonal_iff_twoEdgeSigma_or_v1
    {f : Nat -> Nat -> Nat} {q v : Nat} (hq : 0 < q) :
    B f q q v <->
      TwoEdgeSigma f q v \/ v = f q (q - 1) := by
  constructor
  · intro hv
    rcases hv with hR | hC
    · rcases hR with ⟨a, haq, hvalue⟩
      have hale : a <= q := Nat.le_of_lt haq
      apply Or.inl
      exact Or.inl ⟨a, haq, by simpa [Nat.min_eq_left hale] using hvalue⟩
    · rcases hC with ⟨b, hbq, hvalue⟩
      by_cases hb : b + 1 < q
      · exact Or.inl (Or.inr ⟨b, hb, hvalue⟩)
      · have hbeq : b = q - 1 := by omega
        subst b
        exact Or.inr hvalue.symm
  · intro hv
    rcases hv with hsigma | hv1
    · rcases hsigma with hdiag | hprefix
      · rcases hdiag with ⟨a, haq, hvalue⟩
        have hale : a <= q := Nat.le_of_lt haq
        exact Or.inl ⟨a, haq, by simpa [Nat.min_eq_left hale] using hvalue⟩
      · rcases hprefix with ⟨b, hbq, hvalue⟩
        exact Or.inr ⟨b, by omega, hvalue⟩
    · exact Or.inr ⟨q - 1, by omega, hv1.symm⟩

/-- Generic top-two-hole theorem for any exact Brouwer recurrence with
diagonal values strictly above their indices. -/
theorem top_two_positive_holes_of_recurrence
    {f : Nat -> Nat -> Nat}
    (hrec : BrouwerRecurrence f)
    (hdiag : forall a, a < f a a)
    {q : Nat} (hq : 0 < q) :
    IsFirstTwoPositiveHoles (TwoEdgeSigma f q)
      (f q (q - 1)) (f q q) := by
  have hv1Mex : IsMex (B f q (q - 1)) (f q (q - 1)) := by
    apply hrec.2 (by omega)
    intro hcarry
    rcases hcarry with ⟨_hcol, hsmall⟩
    have hd := hdiag (q - 1)
    omega
  have hdiagMex : IsMex (B f q q) (f q q) := by
    apply hrec.2 (Nat.le_refl q)
    omega
  constructor
  · change IsMex (TwoEdgeSigma f q) (f q (q - 1))
    rcases hv1Mex with ⟨hpos, habsent, hbelow⟩
    refine ⟨hpos, ?_, ?_⟩
    · intro hsigma
      exact habsent ((B_v1_iff_twoEdgeSigma hq).2 hsigma)
    · intro k hkpos hklt
      exact (B_v1_iff_twoEdgeSigma hq).1 (hbelow k hkpos hklt)
  · change IsMex
      (fun v => TwoEdgeSigma f q v \/ v = f q (q - 1))
      (f q q)
    rcases hdiagMex with ⟨hpos, habsent, hbelow⟩
    refine ⟨hpos, ?_, ?_⟩
    · intro hsigma
      exact habsent ((B_diagonal_iff_twoEdgeSigma_or_v1 hq).2 hsigma)
    · intro k hkpos hklt
      exact
        (B_diagonal_iff_twoEdgeSigma_or_v1 hq).1
          (hbelow k hkpos hklt)

/-- The exact Brouwer recurrence available for the encoded game table. -/
theorem gameF_brouwerRecurrence : BrouwerRecurrence gameF :=
  recurrence_of_encoding_and_mex game_encodes game_complete
    (mex_branch_of_encoding_and_lower game_encodes game_complete
      game_lower_blocked)

/-- In every positive game row, V1 and the diagonal are exactly the first
two positive holes of the two-edge source. -/
theorem gameF_top_two_positive_holes {q : Nat} (hq : 0 < q) :
    IsFirstTwoPositiveHoles (TwoEdgeSigma gameF q)
      (gameF q (q - 1)) (gameF q q) := by
  exact top_two_positive_holes_of_recurrence
    gameF_brouwerRecurrence gameRecurrenceModel.diagonal_gt hq

/-- Row-`t+1` form matching the V-catch convention. -/
theorem gameF_nextRow_top_two_positive_holes (t : Nat) :
    IsFirstTwoPositiveHoles (TwoEdgeSigma gameF (t + 1))
      (gameF (t + 1) t) (gameF (t + 1) (t + 1)) := by
  simpa using gameF_top_two_positive_holes (q := t + 1) (by omega)

/-- The V1 value is the first positive `TwoEdgeSigma` hole. -/
theorem gameF_v1_is_first_positive_hole {q : Nat} (hq : 0 < q) :
    IsFirstPositiveHole (TwoEdgeSigma gameF q) (gameF q (q - 1)) :=
  (gameF_top_two_positive_holes hq).1

/-- After adjoining V1, the diagonal is the first positive hole; hence it
is the second positive `TwoEdgeSigma` hole. -/
theorem gameF_diagonal_is_second_positive_hole {q : Nat} (hq : 0 < q) :
    IsFirstPositiveHole
      (fun v => TwoEdgeSigma gameF q v \/ v = gameF q (q - 1))
      (gameF q q) :=
  (gameF_top_two_positive_holes hq).2

#print axioms gameF_top_two_positive_holes
#print axioms gameF_nextRow_top_two_positive_holes

end ChompLean
