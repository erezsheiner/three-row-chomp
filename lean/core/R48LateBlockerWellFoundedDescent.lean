import R47GeneralLateBlockerParametricNormalForm

set_option autoImplicit false

namespace ChompLean

/-!
R48: well-founded/amortized package for the general late-blocker normal form.

R47 says every first-gap late blocker is either a high-`q` packet or a
boundary packet.  In the boundary packet, the only recursive late-blocker
alternative is `BoundaryCorridorSmallerLateBlocker`, whose blocker is the
next first gap and is strictly smaller.

We therefore declare every nonrecursive R47 outcome terminal and expose an
exact terminal-or-successor-descent theorem.  The descent measure is the
natural-number blocker value, so the relation is well founded.  A run of
`n` recursive late-blocker transitions starting at value `z` has `n<=z`.

No RM2, UnitDip, boundary assumption, or near-midpoint equality is used.
-/

noncomputable def LateBlockerValue (s : Nat) : Nat :=
  DipFirstGap gameRecurrenceModel s

/-- All R47 outcomes which do not require a recursive call to the next
first-gap late blocker. -/
def LateBlockerTerminalCertificate (s : Nat) : Prop :=
  LateBlockerHighQGapPacket s \/
    (BoundaryLateBlockerParametricNormalForm s /\
      Not (BoundaryCorridorSmallerLateBlocker s))

/-- The recursive edge selected by R47. -/
def LateBlockerDescentStep (next current : Nat) : Prop :=
  next = current + 1 /\
  DipFirstGapLateBlockerLoss gameRecurrenceModel next /\
  LateBlockerValue next < LateBlockerValue current

/-- Every late blocker is terminal or makes one strict successor descent. -/
theorem gameF_late_blocker_terminal_or_successor_descent
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    LateBlockerTerminalCertificate s \/
      LateBlockerDescentStep (s + 1) s := by
  rcases gameF_dip_first_gap_late_blocker_parametric_normal_form hLate with
    hBoundary | hHigh
  · by_cases hSmaller : BoundaryCorridorSmallerLateBlocker s
    · right
      dsimp [BoundaryCorridorSmallerLateBlocker] at hSmaller
      exact ⟨rfl, hSmaller.1, hSmaller.2.1⟩
    · left
      exact Or.inr ⟨hBoundary, hSmaller⟩
  · left
    exact Or.inl hHigh

/-- The late-blocker successor relation is well founded by the blocker
value measure. -/
theorem gameF_late_blocker_descent_wellFounded :
    WellFounded LateBlockerDescentStep := by
  constructor
  intro s
  generalize hn : LateBlockerValue s = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
      constructor
      intro next hstep
      have hlt : LateBlockerValue next < n := by
        rw [← hn]
        exact hstep.2.2
      exact ih (LateBlockerValue next) hlt next rfl

/-- A finite run of recursive R48 choices along successive rows. -/
def LateBlockerDescentRun (s n : Nat) : Prop :=
  forall k, k < n ->
    DipFirstGapLateBlockerLoss gameRecurrenceModel (s + k) /\
    DipFirstGapLateBlockerLoss gameRecurrenceModel (s + k + 1) /\
    LateBlockerValue (s + k + 1) < LateBlockerValue (s + k)

/-- Amortized packing bound: every recursive transition consumes at least
one unit of blocker value. -/
theorem gameF_late_blocker_descent_run_length_bound :
    forall n s, LateBlockerDescentRun s n -> n <= LateBlockerValue s := by
  intro n
  induction n with
  | zero =>
      intro s _hrun
      omega
  | succ n ih =>
      intro s hrun
      have hfirst := hrun 0 (by omega)
      have hdrop : LateBlockerValue (s + 1) < LateBlockerValue s := by
        simpa using hfirst.2.2
      have htail : LateBlockerDescentRun (s + 1) n := by
        intro k hk
        have hk' := hrun (k + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk'
      have htailBound := ih (s + 1) htail
      omega

/-- No descent run can have more steps than the initial first-gap value.
This contradiction form is convenient for packing arguments. -/
theorem gameF_no_late_blocker_descent_run_longer_than_value
    {s n : Nat}
    (hrun : LateBlockerDescentRun s n)
    (hlong : LateBlockerValue s < n) : False := by
  have hbound := gameF_late_blocker_descent_run_length_bound n s hrun
  omega

end ChompLean
