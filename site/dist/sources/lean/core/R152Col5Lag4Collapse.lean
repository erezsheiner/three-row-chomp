import GameFCol5Rail
import R152Col5AtomicCollapseConditional

set_option autoImplicit false

namespace ChompLean

/-!
R152 actual-game closure of the lag-four face of the R151 first-failure
normal form.  `GameFCol5RailFrom7` is no longer an interface premise: it is
discharged by the recurrence theorem `gameF_col5_rail`.
-/

theorem gameF_col5RailFrom7 : GameFCol5RailFrom7 := by
  intro t ht
  exact gameF_col5_rail ht

/-- The lag-four terminal pattern is impossible for a large blocker even
without midpoint or first-failure hypotheses.  The lag-four host forces
`r=6`, but column six is permanently frozen to blocker 9. -/
theorem gameF_no_lag4_blocker_terminal
    {q r : Nat}
    (hq8 : 8 <= q)
    (hra : r <= q - 1)
    (hstart : gameF (q + 3) r = q + 3)
    (hburn : gameF (q - 1) (r - 1) = q + 3) :
    False := by
  have hr : r = 6 := gameF_col5_lag4_terminal_pins_r
    gameF_col5RailFrom7 hq8 hra hburn
  subst r
  exact gameF_no_high_rowstart_col6 (v := q + 3) (by omega) hstart

/-- No large first-failure frame can end its terminal-predecessor burn on
row `q-1`.  The column-5 rail pins the freeze to column six, while failure
and the midpoint lower bound put `g` simultaneously below five and at
least five. -/
theorem gameF_no_lag4_first_failure
    {q r g : Nat}
    (hq8 : 8 <= q)
    (hra : r <= q - 1)
    (hfailure : g + 1 < r)
    (hburn : gameF (q - 1) (r - 1) = q + 3)
    (hmid : q + 2 <= 2 * g) :
    False := by
  exact gameF_col5_kills_lag4_first_failure gameF_col5RailFrom7
    hq8 hra hfailure hburn hmid

/-- Exact blocker-count midpoint wrapper used by the AssignmentUpper
first-failure induction. -/
theorem gameF_no_lag4_first_failure_midpoint
    {A : Nat -> Nat} {q r g : Nat}
    (hq8 : 8 <= q)
    (hra : r <= q - 1)
    (hfailure : g + 1 < r)
    (hburn : gameF (q - 1) (r - 1) = q + 3)
    (hgdef : q + 2 + A (q + 2) <= 2 * g) :
    False := by
  exact gameF_no_lag4_first_failure hq8 hra hfailure hburn (by omega)

/-- Strengthened R151 normal form: in every large midpoint first failure,
the terminal-predecessor witness is not merely before the lag-three row;
it is strictly before the lag-four row.  Equivalently the remaining burn
has lag at least five from the target `q+3`. -/
theorem gameF_firstFailure_burn_ladder_pre_lag4
    {A : Nat -> Nat} {q r g H : Nat}
    (hq8 : 8 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hgdef : q + 2 + A (q + 2) <= 2 * g) :
    exists a, r <= a /\ a < q - 1 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_normal_form
      (by omega) hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 1
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have hae : a = q - 1 := by omega
    subst a
    exact False.elim
      (gameF_no_lag4_first_failure_midpoint hq8 hra hfailure hburn hgdef)

/-- Midpoint-free strengthened normal form.  The actual freeze at `r`
itself, together with the column-5/column-6 rail pair, already removes the
lag-four endpoint. -/
theorem gameF_firstFailure_burn_ladder_pre_lag4_actual
    {q r g H : Nat}
    (hq8 : 8 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    exists a, r <= a /\ a < q - 1 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_normal_form
      (by omega) hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 1
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have hae : a = q - 1 := by omega
    subst a
    exact False.elim (gameF_no_lag4_blocker_terminal hq8 hra hstart hburn)

/-- The concrete repaired-rank-30 atomic escape is not an actual-game
configuration: row 56 already hosts 60 uniquely at column 5. -/
theorem gameF_excludes_repaired_rank30_atomic_terminal
    (hburn : gameF 56 45 = 60) : False := by
  exact gameF_col5_excludes_repaired_rank30_atomic_terminal
    gameF_col5RailFrom7 hburn

#print axioms gameF_col5RailFrom7
#print axioms gameF_no_lag4_blocker_terminal
#print axioms gameF_no_lag4_first_failure
#print axioms gameF_no_lag4_first_failure_midpoint
#print axioms gameF_firstFailure_burn_ladder_pre_lag4
#print axioms gameF_firstFailure_burn_ladder_pre_lag4_actual
#print axioms gameF_excludes_repaired_rank30_atomic_terminal

end ChompLean
