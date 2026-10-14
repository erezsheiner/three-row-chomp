import R49HighQLateBlockerTerminalPacking

set_option autoImplicit false

namespace ChompLean

/-!
R50: open the source-gap/boundary-owner residue of the high-`q` terminal.

R49 gives a finite charge for the post-freeze gap family.  The R47 packet
also contains a distinguished future gap.  If that gap is not pre-freeze
and has no earlier boundary owner, R27's cell trichotomy says that its
boundary cell is low, serves the blocker, or emits a new high value below
the blocker.  Only the last case recurses, and its row index is strictly
later.  The remaining-height measure `z-t` therefore decreases strictly.

This file packages that iteration as a well-founded relation, proves its
run-length bound, and composes it with the R48 late-blocker descent budget.
No boundary, near-midpoint, RM2, or `UnitDip` hypothesis is used.
-/

/-- A high value below `z` emitted at prefix boundary `c`, while `z` is
still absent from the strict prefix.  This is exactly the input needed for
another R27 future-gap step. -/
def HighQGapSeed (c z t : Nat) : Prop :=
  c < t /\
  t < gameF t c /\ gameF t c < z /\
  Not (C gameF t c z)

/-- Nonrecursive landing cases for an R27 future gap: the gap is still
pre-freeze, has an earlier boundary-column owner, or is a full source gap
whose boundary cell is already low or serves `z`. -/
def HighQGapLandingTerminal (c z r x : Nat) : Prop :=
  x <= r \/
  (exists a, c < a /\ a < x /\ gameF a c = z) \/
  (Not (B gameF x c z) /\
    (gameF x c <= x \/ gameF x c = z))

/-- One recursive R27 step.  The next source gap is genuinely post-freeze
and its row index is strictly later. -/
def HighQGapIterationStep
    (c z r next current : Nat) : Prop :=
  current < next /\ r < next /\ HighQGapSeed c z next

/-- A terminal landing produced from the current high-gap seed. -/
def HighQGapIterationTerminal
    (c z r current : Nat) : Prop :=
  exists next,
    current < next /\ next < z /\
    Not (C gameF next c z) /\
    HighQGapLandingTerminal c z r next

/-- R27 is now an exact proof-control decision: a high-gap seed either
lands in a concrete nonrecursive case or makes a strict later-row step. -/
theorem gameF_high_q_gap_seed_terminal_or_strict_step
    {c z r current : Nat}
    (hSeed : HighQGapSeed c z current)
    (hrz : r < z) (hstart : gameF z r = z) :
    HighQGapIterationTerminal c z r current \/
      exists next, HighQGapIterationStep c z r next current := by
  rcases hSeed with ⟨hct, htq, hqz, hgap⟩
  rcases gameF_future_gap_iteration_normal_form
      (c := c) (t := current) (q := gameF current c)
      (z := z) (r := r) hct rfl htq hqz hgap hrz hstart with
    ⟨next, hnext, hnextz, hnextGap, hcase⟩
  by_cases hpre : next <= r
  · left
    exact ⟨next, hnext, hnextz, hnextGap, Or.inl hpre⟩
  · have hrnext : r < next := by omega
    rcases hcase with hpre' | howner | hsource
    · exact False.elim (hpre hpre')
    · left
      exact ⟨next, hnext, hnextz, hnextGap,
        Or.inr (Or.inl howner)⟩
    · rcases hsource.2 with hlow | hservice | hhigh
      · left
        exact ⟨next, hnext, hnextz, hnextGap,
          Or.inr (Or.inr ⟨hsource.1, Or.inl hlow⟩)⟩
      · left
        exact ⟨next, hnext, hnextz, hnextGap,
          Or.inr (Or.inr ⟨hsource.1, Or.inr hservice⟩)⟩
      · right
        exact ⟨next, hnext, hrnext,
          ⟨by omega, hhigh.1, hhigh.2, hnextGap⟩⟩

/-- Each recursive source-gap step strictly decreases remaining height. -/
theorem gameF_high_q_gap_iteration_step_strict_measure
    {c z r next current : Nat}
    (hstep : HighQGapIterationStep c z r next current) :
    z - next < z - current := by
  dsimp only [HighQGapIterationStep, HighQGapSeed] at hstep
  omega

/-- The internal high-`q` source-gap recursion is well founded. -/
theorem gameF_high_q_gap_iteration_wellFounded
    (c z r : Nat) :
    WellFounded (HighQGapIterationStep c z r) := by
  constructor
  intro current
  generalize hn : z - current = n
  induction n using Nat.strongRecOn generalizing current with
  | ind n ih =>
      constructor
      intro next hstep
      have hlt : z - next < n := by
        rw [← hn]
        exact gameF_high_q_gap_iteration_step_strict_measure hstep
      exact ih (z - next) hlt next rfl

/-- A finite sequence of internal high-`q` source-gap steps. -/
def HighQGapIterationRun
    (c z r start length : Nat) : Prop :=
  exists state : Nat -> Nat,
    state 0 = start /\
    forall k, k < length ->
      HighQGapIterationStep c z r (state (k + 1)) (state k)

/-- Amortized bound for the internal terminal recursion: every step consumes
at least one unit of remaining height. -/
theorem gameF_high_q_gap_iteration_run_length_bound
    {c z r : Nat} :
    forall length start,
      HighQGapIterationRun c z r start length ->
      length <= z - start := by
  intro length
  induction length with
  | zero =>
      intro start _hrun
      omega
  | succ length ih =>
      intro start hrun
      rcases hrun with ⟨state, hzero, hsteps⟩
      have hfirst := hsteps 0 (by omega)
      have hmeasure : z - state 1 < z - start := by
        rw [← hzero]
        simpa using
          (gameF_high_q_gap_iteration_step_strict_measure hfirst)
      let tail : Nat -> Nat := fun k => state (k + 1)
      have htail : HighQGapIterationRun c z r (state 1) length := by
        refine ⟨tail, rfl, ?_⟩
        intro k hk
        have hk' := hsteps (k + 1) (by omega)
        simpa [tail, Nat.add_assoc] using hk'
      have htailBound := ih (state 1) htail
      omega

/-- R49 plus the complete opening of its distinguished R47 future gap.
The only recursive landing is a fresh high-gap seed at a strictly later
row. -/
def LateBlockerHighQIterativeNormalForm (s : Nat) : Prop :=
  let z := LateBlockerValue s
  LateBlockerHighQChargeNormalForm s /\
    exists r x,
      s + 1 <= r /\ r < z /\ gameF z r = z /\
      s + 1 < x /\ x < z /\ Not (C gameF x s z) /\
      (HighQGapLandingTerminal s z r x \/
        HighQGapSeed s z x)

/-- Every high-`q` late-blocker terminal has the stronger iterative normal
form.  Source low/service and boundary-owner cases close immediately; the
remaining source-high case has strictly smaller remaining height. -/
theorem gameF_high_q_terminal_iterative_normal_form
    {s : Nat}
    (hHigh : LateBlockerHighQGapPacket s) :
    LateBlockerHighQIterativeNormalForm s := by
  dsimp only [LateBlockerHighQIterativeNormalForm, LateBlockerValue]
  refine ⟨gameF_high_q_terminal_charge_normal_form hHigh, ?_⟩
  dsimp only [LateBlockerHighQGapPacket] at hHigh
  rcases hHigh with
    ⟨b, r, x, hbs, hrLate, hrz, hpreview, hstart, hhalf,
      hqHigh, hqz, hxLate, hxz, hxgap, hxcase⟩
  refine ⟨r, x, hrLate, hrz, hstart, hxLate, hxz, hxgap, ?_⟩
  rcases hxcase with hpre | hsource | howner
  · exact Or.inl (Or.inl hpre)
  · have hcell := source_gap_cell_low_or_service_or_high_lower
      gameRecurrenceModel (c := s) (x := x)
      (z := DipFirstGap gameRecurrenceModel s)
      (by omega) (by omega) hsource
    rcases hcell with hlow | hservice | hhigh
    · exact Or.inl
        (Or.inr (Or.inr ⟨hsource, Or.inl hlow⟩))
    · exact Or.inl
        (Or.inr (Or.inr ⟨hsource, Or.inr hservice⟩))
    · exact Or.inr ⟨by omega, hhigh.1, hhigh.2, hxgap⟩
  · exact Or.inl (Or.inr (Or.inl howner))

/-- R50 opens the high-`q` branch of every R48 terminal certificate while
preserving the nonrecursive boundary branch. -/
theorem gameF_late_blocker_terminal_certificate_R50_reduction
    {s : Nat}
    (hTerminal : LateBlockerTerminalCertificate s) :
    LateBlockerHighQIterativeNormalForm s \/
      (BoundaryLateBlockerParametricNormalForm s /\
        Not (BoundaryCorridorSmallerLateBlocker s)) := by
  dsimp only [LateBlockerTerminalCertificate] at hTerminal
  rcases hTerminal with hHigh | hBoundary
  · exact Or.inl (gameF_high_q_terminal_iterative_normal_form hHigh)
  · exact Or.inr hBoundary

/-- Global composition with R48.  After `n` late-blocker descents, the
high-`q` terminal either closes locally or starts an internal well-founded
source-gap recursion.  Its remaining-height budget is strictly smaller than
the full terminal interval, and every run satisfies one explicit additive
bound with the original R48 budget. -/
theorem gameF_descent_to_high_q_internal_iteration_global_bound
    {s n : Nat}
    (hrun : LateBlockerDescentRun s n)
    (hHigh : LateBlockerHighQGapPacket (s + n)) :
    exists r x,
      s + n + 1 <= r /\
      r < LateBlockerValue (s + n) /\
      gameF (LateBlockerValue (s + n)) r =
        LateBlockerValue (s + n) /\
      s + n + 1 < x /\ x < LateBlockerValue (s + n) /\
      Not (C gameF x (s + n) (LateBlockerValue (s + n))) /\
      (HighQGapLandingTerminal
          (s + n) (LateBlockerValue (s + n)) r x \/
        (HighQGapSeed (s + n) (LateBlockerValue (s + n)) x /\
          LateBlockerValue (s + n) - x <
            LateBlockerValue (s + n) - (s + n + 1) /\
          forall length,
            HighQGapIterationRun
                (s + n) (LateBlockerValue (s + n)) r x length ->
            n + length <=
              LateBlockerValue s +
                (LateBlockerValue (s + n) - x))) := by
  have hn := gameF_late_blocker_descent_run_length_bound n s hrun
  have hNF := gameF_high_q_terminal_iterative_normal_form hHigh
  dsimp only [LateBlockerHighQIterativeNormalForm] at hNF
  rcases hNF with
    ⟨_hCharge, r, x, hrLate, hrz, hstart,
      hxLate, hxz, hxgap, hcase⟩
  refine ⟨r, x, hrLate, hrz, hstart,
    hxLate, hxz, hxgap, ?_⟩
  rcases hcase with hterminal | hseed
  · exact Or.inl hterminal
  · right
    refine ⟨hseed, by omega, ?_⟩
    intro length hIteration
    have hm := gameF_high_q_gap_iteration_run_length_bound
      (c := s + n) (z := LateBlockerValue (s + n))
      (r := r) (length := length) (start := x) hIteration
    exact Nat.add_le_add hn hm

end ChompLean

