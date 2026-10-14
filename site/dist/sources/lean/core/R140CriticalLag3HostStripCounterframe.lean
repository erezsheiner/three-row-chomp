import R138StrictPreLag3HostCeilingReduction
import R54WideBoundaryChronologyExclusion

set_option autoImplicit false

namespace ChompLean

/-!
R140: arithmetic audit of the critical lag-three host strip.

There are two positive reductions in this file.

* The banked one-third/one-half rails give only linear-width bounds between
  the first arithmetic candidate `a0` and the blocker midpoint `g`.
* At a critical site, the hypothetical crossing row
  `t = v - A(v-1) - 1 = a+b+3` lies at least two columns left of `g`.
  Thus a branch-free lag-three host in `[g-2,g]` would kill the bad diagonal
  branch without using the candidate window.

The last part records two no-go facts.  A parametric counting skeleton has
an unbounded `a0-g` gap while preserving the exact critical and midpoint
arithmetic.  Also, a blocker-scoped host ceiling is vacuous on the range
branch and therefore cannot manufacture host existence.
-/

/-- Subtraction-free membership in the arithmetic candidate window
`|v-(x+A(x)+1)| <= 2`. -/
def CriticalCandidate (A : Nat -> Nat) (v x : Nat) : Prop :=
  v <= x + A x + 3 /\ x + A x <= v + 1

/-- The strongest bounds supplied by the banked one-third/one-half rails.

The first pair bounds the arithmetic candidate, the second pair bounds the
midpoint.  The final pair makes explicit that the resulting comparison has
linear, rather than constant, width. -/
theorem critical_candidate_midpoint_all_index_bounds
    {A : Nat -> Nat} {v a b g a0 : Nat}
    (hcritical : v = 2 * a + b + 4)
    (hmidLower : 2 * g <= v + a)
    (hmidUpper : v + a < 2 * g + 2)
    (haLower : a + 2 <= 3 * b)
    (haUpper : 2 * b + 3 <= a)
    (hcandidate : CriticalCandidate A v a0)
    (hcandidateLower : a0 + 2 <= 3 * A a0)
    (hcandidateUpper : 2 * A a0 + 3 <= a0) :
    2 * v <= 3 * a0 + 3 /\
      4 * a0 <= 3 * v + 1 /\
      7 * v <= 10 * g + 10 /\
      7 * g + 7 <= 5 * v /\
      21 * g <= 21 * a0 + v /\
      20 * a0 <= 20 * g + v + 25 := by
  rcases hcandidate with ⟨hcLo, hcHi⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- Exact critical crossing coordinate after eliminating `v`.

At `E(v-1)=-3`, `a=A(v-1)` and `b=A(a)` give
`v=2a+b+4`; hence `t=v-a-1=a+b+3`. -/
theorem critical_crossing_coordinate
    {v a b t : Nat}
    (hcritical : v = 2 * a + b + 4)
    (ht : t = v - a - 1) :
    t = a + b + 3 := by
  omega

/-- The critical crossing row is at least two columns left of the midpoint.

Only the sharp blocker-count upper rail at `a`, a tiny base condition, and
the defining midpoint inequalities are used. -/
theorem critical_crossing_two_left_of_midpoint
    {v a b t g : Nat}
    (hcritical : v = 2 * a + b + 4)
    (ht : t = a + b + 3)
    (hb : 3 <= b)
    (haUpper : 2 * b + 3 <= a)
    (hmidUpper : v + a < 2 * g + 2) :
    t + 2 <= g := by
  omega

/-- Any column in `[g-2,g]` is to the right of the critical crossing row. -/
theorem critical_midpoint_strip_right_of_crossing
    {t g h : Nat}
    (htg : t + 2 <= g)
    (hh : g - 2 <= h) :
    t <= h := by
  omega

/-- A past diagonal at row `t<=h` is literally present in the Brouwer source
of the later cell `(v-3,h)`.  The equality case uses column history because
`min t h=t`. -/
theorem gameF_past_diagonal_visible_in_lag3_source
    {v t h : Nat}
    (hth : t <= h)
    (hhRow : h < v - 3)
    (hdiag : gameF t t = v) :
    B gameF (v - 3) h v := by
  left
  refine ⟨t, by omega, ?_⟩
  have hmin : min t h = t := Nat.min_eq_left hth
  simpa [hmin] using hdiag

/-- Actual-game form of the three-column reduction.  A high host is an
exact MEX cell, hence its value is absent from its literal source.  The past
diagonal theorem puts the same value in that source. -/
theorem gameF_critical_midpoint_lag3_host_kills_bad_diagonal
    {v t g : Nat}
    (htg : t + 2 <= g)
    (hdiag : gameF t t = v)
    (hstripHost : exists h,
      g - 2 <= h /\ h <= g /\ h < v - 3 /\
        gameF (v - 3) h = v) :
    False := by
  rcases hstripHost with ⟨h, hhLo, _hhHi, hhRow, hhValue⟩
  have hth : t <= h := critical_midpoint_strip_right_of_crossing htg hhLo
  have hsource : B gameF (v - 3) h v :=
    gameF_past_diagonal_visible_in_lag3_source hth hhRow hdiag
  have hmex : IsMex (B gameF (v - 3) h) v :=
    gameF_high_cell_exact_mex (Nat.le_of_lt hhRow) (by omega) hhValue
  exact hmex.2.1 hsource

/-- Abstract MEX-source reduction.

`hbadNoHost` is exactly the source-exclusion consequence of the bad branch
`d(t)=v`: once `t<=h`, the diagonal value `v` already belongs to the source
of the cell `(v-3,h)`, so that cell cannot emit `v`.  Consequently a
branch-free host in `[g-2,g]` closes the bad branch. -/
theorem critical_midpoint_lag3_host_kills_bad_diagonal
    {F : Nat -> Nat -> Nat} {v t g : Nat}
    (htg : t + 2 <= g)
    (hbadNoHost : forall h,
      t <= h -> h < v - 3 -> F (v - 3) h ≠ v)
    (hstripHost : exists h,
      g - 2 <= h /\ h <= g /\ h < v - 3 /\ F (v - 3) h = v) :
    False := by
  rcases hstripHost with ⟨h, hhLo, _hhHi, hhRow, hhValue⟩
  have hth : t <= h := critical_midpoint_strip_right_of_crossing htg hhLo
  exact (hbadNoHost h hth hhRow) hhValue

/-- Candidate-frontier and midpoint-strip hosts are not formally identical.
The implication from a strip host to CFLH needs the extra phase inequality
`a0-1 <= g-K`. -/
theorem midpoint_strip_host_implies_candidate_frontier_host
    {F : Nat -> Nat -> Nat} {v a0 g K : Nat}
    (hphase : a0 - 1 <= g - K)
    (hstrip : exists h,
      g - K <= h /\ h <= g /\ h < v - 3 /\ F (v - 3) h = v) :
    exists h, a0 - 1 <= h /\ h < v - 3 /\ F (v - 3) h = v := by
  rcases hstrip with ⟨h, hhLo, _hhHi, hhRow, hhValue⟩
  have hhFrontier : a0 - 1 <= h := by omega
  exact ⟨h, hhFrontier, hhRow, hhValue⟩

/-- Conversely, CFLH plus an independent host upper bound gives a fixed
strip only after the opposite phase inequality `g-K <= a0-1` is supplied. -/
theorem candidate_frontier_host_implies_midpoint_strip_host
    {F : Nat -> Nat -> Nat} {v a0 g K : Nat}
    (hphase : g - K <= a0 - 1)
    (hhostUpper : forall h,
      F (v - 3) h = v -> h <= g)
    (hcflh : exists h,
      a0 - 1 <= h /\ h < v - 3 /\ F (v - 3) h = v) :
    exists h, g - K <= h /\ h <= g /\ h < v - 3 /\ F (v - 3) h = v := by
  rcases hcflh with ⟨h, hhLo, hhRow, hhValue⟩
  have hhStrip : g - K <= h := by omega
  exact ⟨h, hhStrip, hhostUpper h hhValue, hhRow, hhValue⟩

/-- Blocker-scoped form of HOST-THROUGH. -/
def ScopedHostThrough
    (IsBlocker : Nat -> Prop) (F : Nat -> Nat -> Nat)
    (v g : Nat) : Prop :=
  IsBlocker v ->
    forall r c, r <= v - 3 -> F r c = v -> c <= g

/-- A literal logical countermodel to the attempted use of HOST-THROUGH for
host existence.  On the range branch `IsBlocker v` is false, so the ceiling
is true while the lag-three row has no `v` host at all. -/
theorem scoped_host_through_does_not_supply_host_existence
    {v g : Nat} (hv : 0 < v) :
    let IsBlocker : Nat -> Prop := fun _ => False
    let F : Nat -> Nat -> Nat := fun _ _ => 0
    ScopedHostThrough IsBlocker F v g /\
      Not (exists h, F (v - 3) h = v) := by
  dsimp [ScopedHostThrough]
  constructor
  · intro hfalse
    exact False.elim hfalse
  · rintro ⟨h, hh⟩
    omega

/-! ### Parametric arithmetic counterframe -/

def r140AIndex (j : Nat) : Nat := 420 * j
def r140BIndex (j : Nat) : Nat := 210 * j - 2
def r140V (j : Nat) : Nat := 1050 * j + 2
def r140N (j : Nat) : Nat := 1050 * j + 1
def r140G (j : Nat) : Nat := 735 * j + 1
def r140A0 (j : Nat) : Nat := 750 * j - 1

/-- Tail of the counting counterframe used in the report.  Below
`420j` it follows the sharp half-density rail; above it, it follows a
two-in-five word. -/
def r140CounterA (j n : Nat) : Nat :=
  if n <= r140AIndex j then n / 2 - 2
  else max (r140BIndex j) ((2 * (n - 1) + 4) / 5)

theorem r140_counterframe_selected_values (j : Nat) (hj : 1 <= j) :
    r140CounterA j (r140AIndex j) = r140BIndex j /\
      r140CounterA j (r140N j) = r140AIndex j /\
      r140CounterA j (r140G j) = 294 * j /\
      r140CounterA j (r140A0 j) = 300 * j /\
      r140CounterA j (r140A0 j - 1) = 300 * j - 1 := by
  simp only [r140CounterA, r140AIndex, r140BIndex, r140N, r140G, r140A0]
  constructor
  · rw [if_pos (by omega)]
    omega
  constructor
  · rw [if_neg (by omega)]
    have hmax : max (210 * j - 2)
          ((2 * (1050 * j + 1 - 1) + 4) / 5) =
        ((2 * (1050 * j + 1 - 1) + 4) / 5) := by
      apply Nat.max_eq_right
      omega
    rw [hmax]
    omega
  constructor
  · rw [if_neg (by omega)]
    have hmax : max (210 * j - 2) ((2 * (735 * j + 1 - 1) + 4) / 5) =
        ((2 * (735 * j + 1 - 1) + 4) / 5) := by
      apply Nat.max_eq_right
      omega
    rw [hmax]
    omega
  constructor
  · rw [if_neg (by omega)]
    have hmax : max (210 * j - 2) ((2 * (750 * j - 1 - 1) + 4) / 5) =
        ((2 * (750 * j - 1 - 1) + 4) / 5) := by
      apply Nat.max_eq_right
      omega
    rw [hmax]
    omega
  · rw [if_neg (by omega)]
    have hmax : max (210 * j - 2)
          ((2 * (750 * j - 1 - 1 - 1) + 4) / 5) =
        ((2 * (750 * j - 1 - 1 - 1) + 4) / 5) := by
      apply Nat.max_eq_right
      omega
    rw [hmax]
    omega

/-- The frame has the exact critical `E=-3` equality and exact midpoint. -/
theorem r140_counterframe_critical_midpoint (j : Nat) (hj : 1 <= j) :
    r140V j = 2 * r140AIndex j + r140BIndex j + 4 /\
      r140N j = r140V j - 1 /\
      r140CounterA j (r140N j) = r140AIndex j /\
      r140CounterA j (r140AIndex j) +
          2 * r140CounterA j (r140N j) + 3 = r140N j /\
      2 * r140G j = r140V j + r140AIndex j := by
  have hs := r140_counterframe_selected_values j hj
  rcases hs with ⟨hAa, hAN, _hAg, _hAa0, _hAprev⟩
  simp [r140V, r140AIndex, r140BIndex, r140N, r140G] at *
  omega

/-- The candidate crossing lies `15j-2` columns to the right of `g`.
The two displayed source sums certify that `a0` is the first point at which
the monotone candidate map can enter the window. -/
theorem r140_counterframe_unbounded_candidate_gap
    (j : Nat) (hj : 1 <= j) :
    r140A0 j = r140G j + (15 * j - 2) /\
      r140A0 j + r140CounterA j (r140A0 j) + 1 + 2 = r140V j /\
      (r140A0 j - 1) + r140CounterA j (r140A0 j - 1) + 1 + 4 =
        r140V j := by
  have hs := r140_counterframe_selected_values j hj
  rcases hs with ⟨_hAa, _hAN, _hAg, hAa0, hAprev⟩
  simp [r140A0, r140G, r140V] at *
  omega

#print axioms critical_candidate_midpoint_all_index_bounds
#print axioms critical_crossing_two_left_of_midpoint
#print axioms critical_midpoint_lag3_host_kills_bad_diagonal
#print axioms gameF_critical_midpoint_lag3_host_kills_bad_diagonal
#print axioms scoped_host_through_does_not_supply_host_existence
#print axioms r140_counterframe_critical_midpoint
#print axioms r140_counterframe_unbounded_candidate_gap

end ChompLean
