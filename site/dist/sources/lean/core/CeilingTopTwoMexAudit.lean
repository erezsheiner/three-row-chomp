import ChompLean.Proof

set_option autoImplicit false

namespace ChompLean

/--
The theorem-grade V-cell normal form.  `V1` and the diagonal are always MEX
cells.  `V2` is either a carry of yesterday's `V1`, or a genuine MEX cell.

This deliberately states only what follows from the recurrence; blocker/range
candidate classifications require additional chronology hypotheses.
-/
theorem ceiling_top_two_mex_branches
    {f : Nat -> Nat -> Nat}
    (hrec : BrouwerRecurrence f)
    (hdiag : forall a, a < f a a) (r : Nat) :
    IsMex (B f (r + 2) (r + 1)) (f (r + 2) (r + 1)) /\
    IsMex (B f (r + 2) (r + 2)) (f (r + 2) (r + 2)) /\
    ((f (r + 1) r < r + 2 /\ f (r + 2) r = f (r + 1) r) \/
     (r + 2 <= f (r + 1) r /\
      IsMex (B f (r + 2) r) (f (r + 2) r))) := by
  have hv1 : IsMex (B f (r + 2) (r + 1)) (f (r + 2) (r + 1)) := by
    apply hrec.2 (by omega)
    intro hfirst
    have hd := hdiag (r + 1)
    have hsmall := hfirst.2
    have hidx : r + 2 - 1 = r + 1 := by omega
    rw [hidx] at hsmall
    omega
  have hdMex : IsMex (B f (r + 2) (r + 2)) (f (r + 2) (r + 2)) := by
    apply hrec.2 (by omega)
    omega
  have hsplit :
      (f (r + 1) r < r + 2 /\ f (r + 2) r = f (r + 1) r) \/
      (r + 2 <= f (r + 1) r /\
       IsMex (B f (r + 2) r) (f (r + 2) r)) := by
    by_cases hcarry : f (r + 1) r < r + 2
    case pos =>
      apply Or.inl
      apply And.intro hcarry
      have h := hrec.1 (q := r + 2) (r := r) (by omega) (by
        have hidx : r + 2 - 1 = r + 1 := by omega
        rw [hidx]
        exact hcarry)
      exact h
    case neg =>
      apply Or.inr
      apply And.intro (Nat.le_of_not_gt hcarry)
      apply hrec.2 (by omega)
      intro hfirst
      have hsmall := hfirst.2
      have hidx : r + 2 - 1 = r + 1 := by omega
      rw [hidx] at hsmall
      exact hcarry hsmall
  exact ⟨hv1, hdMex, hsplit⟩

/-- A mex is the least positive source hole. -/
theorem ceiling_least_hole_of_mex
    {S : Nat -> Prop} {m : Nat} (hm : IsMex S m) :
    Not (S m) /\ forall z, 0 < z -> Not (S z) -> m <= z := by
  constructor
  · exact hm.2.1
  · intro z hz hnot
    apply Nat.le_of_not_gt
    intro hzm
    exact hnot (hm.2.2 z hz hzm)

end ChompLean
