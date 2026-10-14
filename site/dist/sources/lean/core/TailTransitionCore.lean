import R15ParkedValueSwap
import LineHolePreservation

set_option autoImplicit false

namespace ChompLean

/-!
Exact source algebra for the slanted-tail transition.

These lemmas contain no finite-data assumptions.  They isolate the current
row host and the genuinely column-dependent `ColTail` channel of a row-start
value, and identify a vertical hole birth with eviction from the replaced row
prefix.
-/

/-- For a row-start value with known current-row host `b`, membership in an
arbitrary source is exactly old-column membership or placement of the host
strictly before the source column. -/
theorem rowstart_source_iff_colTail_or_host_before
    (M : RecurrenceModel) {q c z s b : Nat}
    (hsz : s < z) (hstart : M.f z s = z)
    (hcq : c <= q) (hbq : b <= q) (hhost : M.f q b = z) :
    B M.f q c z <-> ColTail M.f q c z \/ b < c := by
  constructor
  · intro hsource
    rcases hsource with hhistory | hprefix
    · rcases R_iff_diagPrefix_or_colTail.mp hhistory with hdiag | htail
      · rcases hdiag with ⟨a, haq, _hac, hvalue⟩
        exact False.elim
          (disjoint_D_S M ⟨a, hvalue⟩ ⟨s, hsz, hstart⟩)
      · exact Or.inl htail
    · rcases hprefix with ⟨b', hb'c, hvalue⟩
      have hb'q : b' <= q := by omega
      have heq : b' = b :=
        M.fixed_q_injective hb'q hbq (hvalue.trans hhost.symm)
      exact Or.inr (by omega)
  · intro h
    rcases h with htail | hbc
    · exact Or.inl (R_iff_diagPrefix_or_colTail.mpr (Or.inr htail))
    · exact Or.inr ⟨b, hbc, hhost⟩

/-- Hole form of `rowstart_source_iff_colTail_or_host_before`. -/
theorem rowstart_source_hole_iff_no_colTail_and_host_not_left
    (M : RecurrenceModel) {q c z s b : Nat}
    (hsz : s < z) (hstart : M.f z s = z)
    (hcq : c <= q) (hbq : b <= q) (hhost : M.f q b = z) :
    Not (B M.f q c z) <->
      Not (ColTail M.f q c z) /\ c <= b := by
  have hiff := rowstart_source_iff_colTail_or_host_before
    M hsz hstart hcq hbq hhost
  constructor
  · intro h
    constructor
    · intro htail
      exact h (hiff.mpr (Or.inl htail))
    · apply Nat.le_of_not_gt
      intro hbc
      exact h (hiff.mpr (Or.inr hbc))
  · rintro ⟨hnoTail, hcb⟩ hsource
    rcases hiff.mp hsource with htail | hbc
    · exact hnoTail htail
    · omega

/-- Exact vertical birth law: a value covered by the old source and missing
from the next-row source at the same column was present only in the discarded
old row prefix. -/
theorem vertical_hole_birth_iff_prefix_eviction
    {f : Nat -> Nat -> Nat} {r c z : Nat}
    (hcr : c <= r) :
    (B f r c z /\ Not (B f (r + 1) c z)) <->
      (C f r c z /\
       Not (R f r c z) /\
       f r c ≠ z /\
       Not (C f (r + 1) c z)) := by
  constructor
  · rintro ⟨hold, hnext⟩
    have hthree :=
      (next_row_hole_iff_three_exclusions
        (f := f) (r := r) (c := c) (y := z) hcr).mp hnext
    have holdPrefix : C f r c z := by
      rcases hold with holdHistory | holdPrefix
      · exact False.elim (hthree.1 holdHistory)
      · exact holdPrefix
    exact ⟨holdPrefix, hthree.1, hthree.2.1, hthree.2.2⟩
  · rintro ⟨holdPrefix, hnoHistory, hnoSubmitter, hnewPrefix⟩
    constructor
    · exact Or.inr holdPrefix
    · exact (next_row_hole_iff_three_exclusions
        (f := f) (r := r) (c := c) (y := z) hcr).mpr
          ⟨hnoHistory, hnoSubmitter, hnewPrefix⟩

/-- Positive MEX uniqueness, stated for the recurrence library's `IsMex`. -/
theorem tail_isMex_unique
    {S : Nat -> Prop} {a b : Nat}
    (ha : IsMex S a) (hb : IsMex S b) :
    a = b := by
  by_cases hab : a < b
  · exact False.elim (ha.2.1 (hb.2.2 a ha.1 hab))
  by_cases hba : b < a
  · exact False.elim (hb.2.1 (ha.2.2 b hb.1 hba))
  omega

/-- DEFERRED-MEX.  Changes at or above a cutoff cannot alter a positive MEX
which lies strictly below that cutoff.  Thus high future tokens may be carried
symbolically until they enter the active lower band. -/
theorem deferred_mex_eq_of_agree_below_cutoff
    {S T : Nat -> Prop} {m n cutoff : Nat}
    (hm : IsMex S m) (hn : IsMex T n)
    (hmCutoff : m < cutoff)
    (hagree : forall y, 0 < y -> y < cutoff -> (S y <-> T y)) :
    m = n := by
  have hmT : IsMex T m := by
    refine ⟨hm.1, ?_, ?_⟩
    · intro hTm
      exact hm.2.1 ((hagree m hm.1 hmCutoff).2 hTm)
    · intro y hyPos hym
      exact (hagree y hyPos (by omega)).1 (hm.2.2 y hyPos hym)
  exact tail_isMex_unique hmT hn

#print axioms rowstart_source_iff_colTail_or_host_before
#print axioms rowstart_source_hole_iff_no_colTail_and_host_not_left
#print axioms vertical_hole_birth_iff_prefix_eviction
#print axioms deferred_mex_eq_of_agree_below_cutoff

end ChompLean
