import R33UnitDipFirstGapTrichotomy
import DipZRehostRM2IndependentAudit

set_option autoImplicit false

namespace ChompLean

/-!
R38: chronology audit of the two diagonal branches in the R33 first-gap
trichotomy.

The past-diagonal branch is not an old-to-new source loss: its diagonal
witness remains in both consecutive diagonal sources.  Exact MEX instead
turns it into a reverse-successor transport episode for the *new* diagonal
value.  The future-diagonal branch is already such a prehost episode.

The first-violation induction can exclude the past branch at a previously
settled row (where the older running maximum is already below the new
diagonal), but not at the current violating row.  The final two lemmas make
this timing, and the resulting circularity boundary, explicit.
-/

/-- A future diagonal value was already interior-hosted on an earlier row.
At its owner row it is absent from the diagonal source by exact MEX. -/
def FutureDiagonalPrehostLoss
    (M : RecurrenceModel) (q a x : Nat) : Prop :=
  q < a /\
    M.f a a = x /\
    C M.f q q x /\
    Not (B M.f a a x)

/-- A past first-gap witness persists in both consecutive diagonal sources;
there is no one-step source loss to which a retention theorem could be
applied. -/
theorem past_first_gap_persists_in_both_diagonal_sources
    (M : RecurrenceModel) {s : Nat}
    (hPast : DipFirstGapPastDiagonal M s) :
    B M.f s s (DipFirstGap M s) /\
      B M.f (s + 1) (s + 1) (DipFirstGap M s) := by
  rcases hPast.2 with ⟨a, ha, haOwner⟩
  constructor
  · left
    refine ⟨a, ha, ?_⟩
    simpa [Nat.min_eq_left (Nat.le_of_lt ha)] using haOwner
  · left
    refine ⟨a, by omega, ?_⟩
    simpa [Nat.min_eq_left (by omega : a <= s + 1)] using haOwner

/--
The useful exact-MEX reduction of the past branch.  If
`d(a)=d(s+1)+1` with `a<s`, then the future diagonal value `d(s+1)` was
already hosted in the strict prefix of row `a`.  It is absent at its owner
row `s+1`.  Thus the apparently static past branch contains a delayed
future-diagonal prehost/loss episode for the predecessor value.
-/
theorem past_first_gap_forces_predecessor_future_prehost_loss
    (M : RecurrenceModel) {s : Nat}
    (hPast : DipFirstGapPastDiagonal M s) :
    exists a,
      a < s /\
      M.f a a = DipFirstGap M s /\
      FutureDiagonalPrehostLoss M a (s + 1)
        (M.f (s + 1) (s + 1)) := by
  rcases hPast.2 with ⟨a, ha, haOwner⟩
  let x := M.f (s + 1) (s + 1)
  have hxPos : 0 < x := by
    dsimp [x]
    have hgt := M.diagonal_gt (s + 1)
    omega
  have hxlt : x < M.f a a := by
    rw [haOwner]
    dsimp [x, DipFirstGap]
    omega
  have hxB : B M.f a a x :=
    (recurrence_diagonal_exact_mex M a).2.2 x hxPos hxlt
  have hxC : C M.f a a x := by
    rcases hxB with hR | hC
    · rcases hR with ⟨i, hi, hvalue⟩
      have hiOwner : M.f i i = x := by
        simpa [Nat.min_eq_left (Nat.le_of_lt hi)] using hvalue
      have hidx : i = s + 1 :=
        diagonal_injective M hiOwner
      omega
    · exact hC
  have hxAbsent : Not (B M.f (s + 1) (s + 1) x) :=
    (recurrence_diagonal_exact_mex M (s + 1)).2.1
  refine ⟨a, ha, haOwner, ?_⟩
  exact ⟨by omega, rfl, hxC, hxAbsent⟩

/-- The R33 future branch is itself a future-diagonal prehost/loss episode;
exact MEX supplies absence at the eventual owner in addition to R33's
absence on the immediately following row. -/
theorem future_first_gap_is_future_prehost_loss
    (M : RecurrenceModel) {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s) :
    exists a,
      s + 1 < a /\
      FutureDiagonalPrehostLoss M s a (DipFirstGap M s) := by
  rcases hFuture.2 with
    ⟨a, ha, haOwner, hOldHost, _hNextAbsent⟩
  have hOwnerAbsent : Not (B M.f a a (DipFirstGap M s)) := by
    rw [← haOwner]
    exact (recurrence_diagonal_exact_mex M a).2.1
  exact ⟨a, ha, by
    exact ⟨by omega, haOwner, hOldHost, hOwnerAbsent⟩⟩

/-- Both diagonal branches reduce to one chronology species, although for
different values and time intervals.  This is a reduction, not an
unconditional exclusion of that species. -/
theorem diagonal_first_gap_branch_forces_future_prehost_loss
    (M : RecurrenceModel) {s : Nat}
    (hDiagonal :
      DipFirstGapPastDiagonal M s \/
        DipFirstGapFutureDiagonalLoss M s) :
    exists q a x, FutureDiagonalPrehostLoss M q a x := by
  rcases hDiagonal with hPast | hFuture
  · rcases past_first_gap_forces_predecessor_future_prehost_loss
      M hPast with ⟨q, _hq, _howner, hloss⟩
    exact ⟨q, s + 1, M.f (s + 1) (s + 1), hloss⟩
  · rcases future_first_gap_is_future_prehost_loss
      M hFuture with ⟨a, _ha, hloss⟩
    exact ⟨s, a, DipFirstGap M s, hloss⟩

/--
First-violation localization.  If the new diagonal already lies strictly
above every diagonal through `s-1`, the first gap cannot be an earlier
diagonal.  The disjunction is predecessor-safe at `s=0`.
-/
theorem past_first_gap_excluded_by_prior_record_margin
    (M : RecurrenceModel) {s : Nat}
    (hPrior : s = 0 \/
      exists j, s = j + 1 /\ RMax M j < M.f (s + 1) (s + 1)) :
    Not (DipFirstGapPastDiagonal M s) := by
  intro hPast
  rcases hPast.2 with ⟨a, ha, haOwner⟩
  rcases hPrior with hs0 | ⟨j, hsj, hmargin⟩
  · omega
  · have haj : a <= j := by omega
    have hle := rmax_ge M j a haj
    rw [haOwner] at hle
    dsimp [DipFirstGap] at hle
    omega

/-- Direct strong-induction form of the previous lemma. -/
theorem past_first_gap_excluded_at_previously_settled_row
    (M : RecurrenceModel) {j : Nat}
    (hSettled : RMax M j < M.f (j + 2) (j + 2)) :
    Not (DipFirstGapPastDiagonal M (j + 1)) := by
  apply past_first_gap_excluded_by_prior_record_margin M
  exact Or.inr ⟨j, rfl, by simpa [Nat.add_assoc] using hSettled⟩

/-- At a row already covered by the strong-induction hypothesis, the R33
trichotomy genuinely has only two branches.  No RM2 assumption at the
current or a future row is used. -/
theorem nonunit_dip_at_previously_settled_row_is_future_or_late
    (M : RecurrenceModel) {j : Nat}
    (hSettled : RMax M j < M.f (j + 2) (j + 2))
    (hgap : DipFirstGap M (j + 1) < M.f (j + 1) (j + 1)) :
    DipFirstGapFutureDiagonalLoss M (j + 1) \/
      DipFirstGapLateBlockerLoss M (j + 1) := by
  rcases nonunit_dip_first_gap_trichotomy M hgap with
    hPast | hFuture | hLate
  · exact False.elim
      (past_first_gap_excluded_at_previously_settled_row M hSettled hPast)
  · exact Or.inl hFuture
  · exact Or.inr hLate

/-- Consequently, only the future-diagonal and late-blocker exclusions are
needed to prove unit depth at a previously settled dip. -/
theorem previously_settled_dip_is_unit_of_no_future_or_late
    (M : RecurrenceModel) {j : Nat}
    (hSettled : RMax M j < M.f (j + 2) (j + 2))
    (hdip : M.f (j + 2) (j + 2) < M.f (j + 1) (j + 1))
    (hNoFuture : Not (DipFirstGapFutureDiagonalLoss M (j + 1)))
    (hNoLate : Not (DipFirstGapLateBlockerLoss M (j + 1))) :
    M.f (j + 2) (j + 2) + 1 = M.f (j + 1) (j + 1) := by
  by_cases hunit :
      M.f (j + 2) (j + 2) + 1 = M.f (j + 1) (j + 1)
  · exact hunit
  · have hgap :
        DipFirstGap M (j + 1) < M.f (j + 1) (j + 1) := by
      have hdip' :
          M.f (j + 1 + 1) (j + 1 + 1) < M.f (j + 1) (j + 1) := by
        simpa [Nat.add_assoc] using hdip
      have hunit' :
          Not (M.f (j + 1 + 1) (j + 1 + 1) + 1 =
            M.f (j + 1) (j + 1)) := by
        simpa [Nat.add_assoc] using hunit
      dsimp only [DipFirstGap]
      omega
    rcases nonunit_dip_at_previously_settled_row_is_future_or_late
      M hSettled hgap with hFuture | hLate
    · exact False.elim (hNoFuture hFuture)
    · exact False.elim (hNoLate hLate)

/-- A past first gap is an RM2 failure at the *current* new diagonal row.
Consequently the induction hypothesis cannot exclude it there without
assuming the very conclusion under proof. -/
theorem past_first_gap_is_current_two_step_record_failure
    (M : RecurrenceModel) {s : Nat}
    (hPast : DipFirstGapPastDiagonal M s) :
    exists a,
      a + 2 <= s + 1 /\
      M.f (s + 1) (s + 1) < M.f a a := by
  rcases hPast.2 with ⟨a, ha, haOwner⟩
  refine ⟨a, by omega, ?_⟩
  rw [haOwner]
  dsimp [DipFirstGap]
  omega

/-- A future first gap transports the same RM2 failure to its later owner.
Minimal-first-violation induction does not exclude a later failure. -/
theorem future_first_gap_forces_delayed_two_step_record_failure
    (M : RecurrenceModel) {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s) :
    exists a,
      s + 2 <= a /\
      M.f a a < M.f s s := by
  rcases hFuture.2 with
    ⟨a, ha, haOwner, _hOldHost, _hNextAbsent⟩
  refine ⟨a, by omega, ?_⟩
  rw [haOwner]
  exact hFuture.1

/-- A clean chronology premise which is sufficient to remove the past
branch: a diagonal predecessor may occur one row earlier (a unit dip), but
not with a delay of two or more rows.  This law is not derived here. -/
def NoDelayedDiagonalPredecessor (M : RecurrenceModel) : Prop :=
  forall {a t}, a + 2 <= t -> M.f a a ≠ M.f t t + 1

/-- RM2 implies the delayed-predecessor chronology law.  Therefore importing
this premise into a proof of RM2 without an independent proof would be
circular. -/
theorem noDelayedDiagonalPredecessor_of_twoStepRecordLaw
    (M : RecurrenceModel) (hRM2 : TwoStepDiagonalRecordLaw M) :
    NoDelayedDiagonalPredecessor M := by
  intro a t hat hEq
  have hlt := hRM2 hat
  rw [hEq] at hlt
  omega

theorem no_past_first_gap_of_noDelayedDiagonalPredecessor
    (M : RecurrenceModel) (hNoDelay : NoDelayedDiagonalPredecessor M) :
    forall s, Not (DipFirstGapPastDiagonal M s) := by
  intro s hPast
  rcases hPast.2 with ⟨a, ha, haOwner⟩
  apply hNoDelay (a := a) (t := s + 1) (by omega)
  simpa [DipFirstGap] using haOwner

/-- Under the additional delayed-predecessor chronology law, the exact
three-obstruction characterization of `UnitDip` reduces to only the future
diagonal and late-blocker loss branches. -/
theorem unitDip_iff_no_future_or_late_first_gap_of_noDelayedPredecessor
    (M : RecurrenceModel) (hNoDelay : NoDelayedDiagonalPredecessor M) :
    UnitDip M <->
      forall s,
        Not (DipFirstGapFutureDiagonalLoss M s) /\
        Not (DipFirstGapLateBlockerLoss M s) := by
  constructor
  · intro hU s
    have hAll := (unitDip_iff_no_first_gap_obstructions M).1 hU s
    exact ⟨hAll.2.1, hAll.2.2⟩
  · intro hNo
    apply (unitDip_iff_no_first_gap_obstructions M).2
    intro s
    exact ⟨
      no_past_first_gap_of_noDelayedDiagonalPredecessor M hNoDelay s,
      (hNo s).1,
      (hNo s).2⟩

/-- The RM2-only specialization in R33 can be sharpened: RM2 excludes both
diagonal branches, not only the future-owner branch.  The remaining branch
is exactly the late blocker loss.  This is downstream of RM2 and is not
available in the first-violation step at the current row. -/
theorem nonunit_dip_first_gap_of_rm2_is_late_blocker_loss
    (M : RecurrenceModel) {s : Nat}
    (hRM2 : TwoStepDiagonalRecordLaw M)
    (hgap : DipFirstGap M s < M.f s s) :
    DipFirstGapLateBlockerLoss M s := by
  rcases nonunit_dip_first_gap_trichotomy M hgap with
    hPast | hFuture | hLate
  · rcases past_first_gap_is_current_two_step_record_failure
      M hPast with ⟨a, hat, hfailure⟩
    have hforward := hRM2 hat
    omega
  · rcases future_first_gap_forces_delayed_two_step_record_failure
      M hFuture with ⟨a, hsa, hfailure⟩
    have hforward := hRM2 hsa
    omega
  · exact hLate

#print axioms past_first_gap_forces_predecessor_future_prehost_loss
#print axioms past_first_gap_excluded_at_previously_settled_row
#print axioms previously_settled_dip_is_unit_of_no_future_or_late
#print axioms unitDip_iff_no_future_or_late_first_gap_of_noDelayedPredecessor
#print axioms nonunit_dip_first_gap_of_rm2_is_late_blocker_loss

end ChompLean
