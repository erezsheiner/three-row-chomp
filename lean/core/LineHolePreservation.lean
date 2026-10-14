import ChompLean.Proof

set_option autoImplicit false

namespace ChompLean

/-!
An exact one-row update lemma for the moving-hole line.

For a fixed column `c` and `c <= r`, the history part of
`B f (r+1) c` is the old history at `(r,c)` plus the single value
`f r c`.  The row-prefix part is replaced by the prefix of row `r+1`.
Thus an old hole can be filled in exactly two ways: by the new
same-column submitter or by the replacement prefix.

For the observed line, the value carried at row `r` is `x` and the
next line value is `y=x+1`.  The clean staircase supplies holes at
*both* `x` and `y` in the old source.  The lower hole `x`, together
with the recurrence, prevents `f r c` from submitting `y`; the only
remaining debt is exclusion of `y` from the replacement prefix.
-/

/--
Source-native guard for a whole strict row prefix: `lo` is a source hole at
every cell left of `c` in row `q`.  Cache verification of such a ray remains
an external receipt; this definition carries no theorem-grade chronology.
-/
def PrefixGuardRay
    (f : Nat -> Nat -> Nat) (q c lo : Nat) : Prop :=
  forall b, b < c -> Not (B f q b lo)

/-- Adding row `r` to the history contributes exactly `f r c`. -/
theorem next_row_history_expansion
    {f : Nat -> Nat -> Nat} {r c y : Nat}
    (hcr : c <= r) :
    R f (r + 1) c y <-> R f r c y \/ f r c = y := by
  constructor
  · rintro ⟨a, ha, hay⟩
    by_cases har : a < r
    · exact Or.inl ⟨a, har, hay⟩
    · right
      have hae : a = r := by omega
      subst a
      simpa [Nat.min_eq_right hcr] using hay
  · intro h
    rcases h with hold | hnew
    · rcases hold with ⟨a, har, hay⟩
      exact ⟨a, by omega, hay⟩
    · refine ⟨r, by omega, ?_⟩
      simpa [Nat.min_eq_right hcr] using hnew

/--
Exact source update: persistent history, one new column entry, and one
replacement row prefix.  The old row prefix does not persist.
-/
theorem next_row_source_expansion
    {f : Nat -> Nat -> Nat} {r c y : Nat}
    (hcr : c <= r) :
    B f (r + 1) c y <->
      R f r c y \/ f r c = y \/ C f (r + 1) c y := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · rcases (next_row_history_expansion (f := f) (y := y) hcr).mp hR with
        hold | hnew
      · exact Or.inl hold
      · exact Or.inr (Or.inl hnew)
    · exact Or.inr (Or.inr hC)
  · intro h
    rcases h with hold | hnew | hC
    · left
      exact (next_row_history_expansion (f := f) (y := y) hcr).mpr
        (Or.inl hold)
    · left
      exact (next_row_history_expansion (f := f) (y := y) hcr).mpr
        (Or.inr hnew)
    · exact Or.inr hC

/-- De Morgan form of the exact three-channel update. -/
theorem next_row_hole_iff_three_exclusions
    {f : Nat -> Nat -> Nat} {r c y : Nat}
    (hcr : c <= r) :
    Not (B f (r + 1) c y) <->
      Not (R f r c y) /\ f r c ≠ y /\ Not (C f (r + 1) c y) := by
  constructor
  · intro hhole
    refine ⟨?_, ?_, ?_⟩
    · intro hold
      exact hhole ((next_row_source_expansion (f := f) (y := y) hcr).mpr
        (Or.inl hold))
    · intro hnew
      exact hhole ((next_row_source_expansion (f := f) (y := y) hcr).mpr
        (Or.inr (Or.inl hnew)))
    · intro hC
      exact hhole ((next_row_source_expansion (f := f) (y := y) hcr).mpr
        (Or.inr (Or.inr hC)))
  · rintro ⟨hhold, hhnew, hhC⟩ hB
    rcases (next_row_source_expansion (f := f) (y := y) hcr).mp hB with
      hold | hnew | hC
    · exact hhold hold
    · exact hhnew hnew
    · exact hhC hC

/--
If `y` was already a hole in the old full source, persistent history is
automatically excluded.  This is the exact two-channel formulation.
-/
theorem old_hole_next_hole_iff_submitter_and_prefix
    {f : Nat -> Nat -> Nat} {r c y : Nat}
    (hcr : c <= r)
    (hyold : Not (B f r c y)) :
    Not (B f (r + 1) c y) <->
      f r c ≠ y /\ Not (C f (r + 1) c y) := by
  constructor
  · intro hnext
    exact ⟨
      (next_row_hole_iff_three_exclusions (f := f) (y := y) hcr).mp hnext |>.2.1,
      (next_row_hole_iff_three_exclusions (f := f) (y := y) hcr).mp hnext |>.2.2⟩
  · rintro ⟨hsubmit, hprefix⟩
    apply (next_row_hole_iff_three_exclusions (f := f) (y := y) hcr).mpr
    exact ⟨(fun hR => hyold (Or.inl hR)), hsubmit, hprefix⟩

/-- Equivalent covered-value form of the two exceptional channels. -/
theorem old_hole_next_covered_iff_submitter_or_prefix
    {f : Nat -> Nat -> Nat} {r c y : Nat}
    (hcr : c <= r)
    (hyold : Not (B f r c y)) :
    B f (r + 1) c y <-> f r c = y \/ C f (r + 1) c y := by
  constructor
  · intro hnext
    rcases (next_row_source_expansion (f := f) (y := y) hcr).mp hnext with
      hold | hsubmit | hprefix
    · exact False.elim (hyold (Or.inl hold))
    · exact Or.inl hsubmit
    · exact Or.inr hprefix
  · intro h
    rcases h with hsubmit | hprefix
    · exact (next_row_source_expansion (f := f) (y := y) hcr).mpr
        (Or.inr (Or.inl hsubmit))
    · exact (next_row_source_expansion (f := f) (y := y) hcr).mpr
        (Or.inr (Or.inr hprefix))

/-- On a MEX branch, any lower positive hole forbids output `y`. -/
theorem mex_lower_hole_forbids_submitter
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hmex : IsMex (B f r c) (f r c)) :
    f r c ≠ y := by
  intro hout
  apply hxhole
  exact hmex.2.2 x hxpos (by omega)

/-- A positive hole bounds a MEX output from above. -/
theorem mex_le_positive_hole
    {S : Nat -> Prop} {m x : Nat}
    (hxpos : 0 < x)
    (hxhole : Not (S x))
    (hmex : IsMex S m) :
    m <= x := by
  apply Nat.le_of_not_gt
  intro hxm
  exact hxhole (hmex.2.2 x hxpos hxm)

/--
A source hole at a recurrence cell bounds that cell by `lo`, provided the
row index itself is at most `lo`.  On the copy branch the output is `<q`; on
the MEX branch the positive `lo`-hole gives the bound directly.
-/
theorem recurrence_guard_hole_bounds_cell
    {f : Nat -> Nat -> Nat} {q b lo : Nat}
    (hrec : BrouwerRecurrence f)
    (hbq : b <= q)
    (hqlo : q <= lo)
    (hlopos : 0 < lo)
    (hguard : Not (B f q b lo)) :
    f q b <= lo := by
  by_cases hcopy : b < q /\ f (q - 1) b < q
  · have hout : f q b = f (q - 1) b := hrec.1 hcopy.1 hcopy.2
    omega
  · have hmex : IsMex (B f q b) (f q b) := hrec.2 hbq hcopy
    exact mex_le_positive_hole hlopos hguard hmex

/--
`PREFIX-GUARD-RAY` implies the pointwise row-prefix cap.  The domain bound
`c<=q+1` is exactly what ensures every `b<c` lies in the recurrence triangle
(`b<=q`); applications to the moving line have the stronger `c<=q`.
-/
theorem prefix_guard_ray_implies_prefix_cap
    {f : Nat -> Nat -> Nat} {q c lo : Nat}
    (hrec : BrouwerRecurrence f)
    (hcq : c <= q + 1)
    (hqlo : q <= lo)
    (hlopos : 0 < lo)
    (hray : PrefixGuardRay f q c lo) :
    forall b, b < c -> f q b <= lo := by
  intro b hbc
  apply recurrence_guard_hole_bounds_cell hrec (by omega) hqlo hlopos
  exact hray b hbc

/--
MEX-branch prefix-only obstruction.  If the old source has holes at a
positive `x` and at a higher value `y`, its output is at most `x`, so the
new same-column entry cannot submit `y`.  Consequently `y` is covered in
the next source exactly when the replacement prefix covers it.
-/
theorem mex_line_step_covered_iff_replacement_prefix_min
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhistory : Not (R f r c y))
    (hmex : IsMex (B f r c) (f r c)) :
    B f (r + 1) c y <-> C f (r + 1) c y := by
  rw [next_row_source_expansion hcr]
  have hsubmit : f r c ≠ y :=
    mex_lower_hole_forbids_submitter hxpos hxy hxhole hmex
  constructor
  · intro h
    rcases h with hR | heq | hprefix
    · exact False.elim (hyhistory hR)
    · exact False.elim (hsubmit heq)
    · exact hprefix
  · exact fun hprefix => Or.inr (Or.inr hprefix)

/-- Hole form of the assumption-minimal MEX prefix-only obstruction. -/
theorem mex_line_step_hole_iff_replacement_prefix_hole_min
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhistory : Not (R f r c y))
    (hmex : IsMex (B f r c) (f r c)) :
    Not (B f (r + 1) c y) <-> Not (C f (r + 1) c y) := by
  rw [mex_line_step_covered_iff_replacement_prefix_min
    hcr hxpos hxy hxhole hyhistory hmex]

/-- Full-old-hole specialization used directly by the observed staircase. -/
theorem mex_line_step_covered_iff_replacement_prefix
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhole : Not (B f r c y))
    (hmex : IsMex (B f r c) (f r c)) :
    B f (r + 1) c y <-> C f (r + 1) c y := by
  exact mex_line_step_covered_iff_replacement_prefix_min
    hcr hxpos hxy hxhole (fun hR => hyhole (Or.inl hR)) hmex

/-- Hole form of the MEX-branch prefix-only obstruction. -/
theorem mex_line_step_hole_iff_replacement_prefix_hole
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhole : Not (B f r c y))
    (hmex : IsMex (B f r c) (f r c)) :
    Not (B f (r + 1) c y) <-> Not (C f (r + 1) c y) := by
  rw [mex_line_step_covered_iff_replacement_prefix
    hcr hxpos hxy hxhole hyhole hmex]

/--
Interval/staircase form.  Above the least old hole `lo`, every old
staircase hole has only the replacement-prefix obstruction.  The endpoint
`lo` is intentionally excluded: the MEX output may itself equal `lo`.
-/
theorem mex_staircase_step_covered_iff_replacement_prefix
    {f : Nat -> Nat -> Nat} {r c lo hi : Nat}
    (hcr : c <= r)
    (hlopos : 0 < lo)
    (hholes : forall z, lo <= z -> z <= hi -> Not (B f r c z))
    (hmex : IsMex (B f r c) (f r c)) :
    forall y, lo < y -> y <= hi ->
      (B f (r + 1) c y <-> C f (r + 1) c y) := by
  intro y hloy hyhi
  exact mex_line_step_covered_iff_replacement_prefix
    hcr hlopos hloy (hholes lo (by omega) (by omega))
      (hholes y (by omega) hyhi) hmex

/-- If the replacement prefix misses the upper staircase, it survives. -/
theorem mex_preserves_staircase_above_floor
    {f : Nat -> Nat -> Nat} {r c lo hi : Nat}
    (hcr : c <= r)
    (hlopos : 0 < lo)
    (hholes : forall z, lo <= z -> z <= hi -> Not (B f r c z))
    (hmex : IsMex (B f r c) (f r c))
    (hprefix : forall y, lo < y -> y <= hi -> Not (C f (r + 1) c y)) :
    forall y, lo < y -> y <= hi -> Not (B f (r + 1) c y) := by
  intro y hloy hyhi
  intro hB
  apply hprefix y hloy hyhi
  exact (mex_staircase_step_covered_iff_replacement_prefix
    hcr hlopos hholes hmex y hloy hyhi).mp hB

/--
A pointwise cap at the old floor excludes every strictly higher value from
the replacement prefix.  Equality with `lo` is allowed (zero margin).
-/
theorem prefix_cap_kills_values_above_floor
    {f : Nat -> Nat -> Nat} {r c lo : Nat}
    (hcap : forall b, b < c -> f (r + 1) b <= lo) :
    forall y, lo < y -> Not (C f (r + 1) c y) := by
  intro y hloy
  rintro ⟨b, hbc, hby⟩
  have hble : f (r + 1) b <= lo := hcap b hbc
  omega

/--
Pointwise-prefix-cap preservation for an old MEX staircase.  This is the
direct formal port for the empirical cap `f(r+1,b) <= lo` for every `b<c`.
The cap is an input here, not a consequence of source algebra.
-/
theorem prefix_cap_preserves_staircase
    {f : Nat -> Nat -> Nat} {r c lo hi : Nat}
    (hcr : c <= r)
    (hlopos : 0 < lo)
    (hholes : forall z, lo <= z -> z <= hi -> Not (B f r c z))
    (hmex : IsMex (B f r c) (f r c))
    (hcap : forall b, b < c -> f (r + 1) b <= lo) :
    forall y, lo < y -> y <= hi -> Not (B f (r + 1) c y) := by
  apply mex_preserves_staircase_above_floor hcr hlopos hholes hmex
  intro y hloy _hyhi
  exact prefix_cap_kills_values_above_floor hcap y hloy

/-- Exact moving-line specialization `y=lo+1`. -/
theorem prefix_cap_preserves_next_line_value
    {f : Nat -> Nat -> Nat} {r c lo : Nat}
    (hcr : c <= r)
    (hlopos : 0 < lo)
    (hlohole : Not (B f r c lo))
    (hnextOldHole : Not (B f r c (lo + 1)))
    (hmex : IsMex (B f r c) (f r c))
    (hcap : forall b, b < c -> f (r + 1) b <= lo) :
    Not (B f (r + 1) c (lo + 1)) := by
  apply (mex_line_step_hole_iff_replacement_prefix_hole
    hcr hlopos (by omega) hlohole hnextOldHole hmex).mpr
  exact prefix_cap_kills_values_above_floor hcap (lo + 1) (by omega)

/--
Under the full recurrence, the submitter is impossible on either branch.
On the copy branch the copied value was already in persistent history; on
the MEX branch the smaller hole `x` prevents output `y`.
-/
theorem recurrence_lower_hole_and_history_gap_forbid_submitter
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhistory : Not (R f r c y)) :
    f r c ≠ y := by
  by_cases hcopy : c < r /\ f (r - 1) c < r
  · have hout : f r c = f (r - 1) c := hrec.1 hcopy.1 hcopy.2
    intro hry
    have hprev : f (r - 1) c = y := by omega
    apply hyhistory
    refine ⟨r - 1, by omega, ?_⟩
    have hcpred : c <= r - 1 := by omega
    simpa [Nat.min_eq_right hcpred] using hprev
  · have hmex : IsMex (B f r c) (f r c) := hrec.2 hcr hcopy
    exact mex_lower_hole_forbids_submitter hxpos hxy hxhole hmex

/-- Convenient full-source-hole specialization of the preceding lemma. -/
theorem recurrence_two_old_holes_forbid_submitter
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhole : Not (B f r c y)) :
    f r c ≠ y :=
  recurrence_lower_hole_and_history_gap_forbid_submitter
    hrec hcr hxpos hxy hxhole (fun hR => hyhole (Or.inl hR))

/--
Minimal recurrence-level line step.  A full old-source hole at `y` is
unnecessary: only absence of `y` from the persistent history is needed.
The discarded old row prefix may contain `y`.
-/
theorem recurrence_line_step_covered_iff_replacement_prefix_min
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhistory : Not (R f r c y)) :
    B f (r + 1) c y <-> C f (r + 1) c y := by
  rw [next_row_source_expansion hcr]
  have hsubmit : f r c ≠ y :=
    recurrence_lower_hole_and_history_gap_forbid_submitter
      hrec hcr hxpos hxy hxhole hyhistory
  constructor
  · intro h
    rcases h with hR | hentry | hprefix
    · exact False.elim (hyhistory hR)
    · exact False.elim (hsubmit hentry)
    · exact hprefix
  · exact fun hprefix => Or.inr (Or.inr hprefix)

/-- Hole form of the minimal recurrence-level line step. -/
theorem recurrence_line_step_hole_iff_replacement_prefix_hole_min
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhistory : Not (R f r c y)) :
    Not (B f (r + 1) c y) <-> Not (C f (r + 1) c y) := by
  rw [recurrence_line_step_covered_iff_replacement_prefix_min
    hrec hcr hxpos hxy hxhole hyhistory]

/--
Strongest recurrence-level one-step reduction for the moving line: once the
old staircase gives holes at both `x<y`, coverage of the next line value is
*equivalent* to coverage by the replacement prefix.
-/
theorem recurrence_line_step_covered_iff_replacement_prefix
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhole : Not (B f r c y)) :
    B f (r + 1) c y <-> C f (r + 1) c y := by
  exact recurrence_line_step_covered_iff_replacement_prefix_min
    hrec hcr hxpos hxy hxhole (fun hR => hyhole (Or.inl hR))

/-- Hole form of the exact line-step reduction. -/
theorem recurrence_line_step_hole_iff_replacement_prefix_hole
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhole : Not (B f r c y)) :
    Not (B f (r + 1) c y) <-> Not (C f (r + 1) c y) := by
  rw [recurrence_line_step_covered_iff_replacement_prefix
    hrec hcr hxpos hxy hxhole hyhole]

/-- Direct preservation corollary used by a descending line induction. -/
theorem recurrence_preserves_next_line_hole
    {f : Nat -> Nat -> Nat} {r c x y : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hxpos : 0 < x) (hxy : x < y)
    (hxhole : Not (B f r c x))
    (hyhole : Not (B f r c y))
    (hreplacement : Not (C f (r + 1) c y)) :
    Not (B f (r + 1) c y) :=
  (recurrence_line_step_hole_iff_replacement_prefix_hole
    hrec hcr hxpos hxy hxhole hyhole).mpr hreplacement

/--
Full-recurrence counterpart of `prefix_cap_preserves_staircase`.  It covers
both the MEX and copy branches; the pointwise prefix cap remains an explicit
open input.
-/
theorem recurrence_prefix_cap_preserves_staircase
    {f : Nat -> Nat -> Nat} {r c lo hi : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hlopos : 0 < lo)
    (hholes : forall z, lo <= z -> z <= hi -> Not (B f r c z))
    (hcap : forall b, b < c -> f (r + 1) b <= lo) :
    forall y, lo < y -> y <= hi -> Not (B f (r + 1) c y) := by
  intro y hloy hyhi
  apply (recurrence_line_step_hole_iff_replacement_prefix_hole
    hrec hcr hlopos hloy
      (hholes lo (by omega) (by omega))
      (hholes y (by omega) hyhi)).mpr
  exact prefix_cap_kills_values_above_floor hcap y hloy

/-- Full-recurrence moving-line specialization `y=lo+1`. -/
theorem recurrence_prefix_cap_preserves_next_line_value
    {f : Nat -> Nat -> Nat} {r c lo : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hlopos : 0 < lo)
    (hlohole : Not (B f r c lo))
    (hnextOldHole : Not (B f r c (lo + 1)))
    (hcap : forall b, b < c -> f (r + 1) b <= lo) :
    Not (B f (r + 1) c (lo + 1)) := by
  apply (recurrence_line_step_hole_iff_replacement_prefix_hole
    hrec hcr hlopos (by omega) hlohole hnextOldHole).mpr
  exact prefix_cap_kills_values_above_floor hcap (lo + 1) (by omega)

/--
Source-native composition:

`PREFIX-GUARD-RAY` on the replacement row
  -> pointwise prefix cap (by recurrence and `r+1<=lo`)
  -> preservation of every old staircase hole strictly above `lo`.

The ray itself is an explicit premise, not proved here.
-/
theorem prefix_guard_ray_preserves_staircase
    {f : Nat -> Nat -> Nat} {r c lo hi : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hnextRowLe : r + 1 <= lo)
    (hlopos : 0 < lo)
    (hholes : forall z, lo <= z -> z <= hi -> Not (B f r c z))
    (hray : PrefixGuardRay f (r + 1) c lo) :
    forall y, lo < y -> y <= hi -> Not (B f (r + 1) c y) := by
  apply recurrence_prefix_cap_preserves_staircase
    hrec hcr hlopos hholes
  apply prefix_guard_ray_implies_prefix_cap
    hrec (by omega) hnextRowLe hlopos hray

/-- Exact `y=lo+1` composition of guard ray and line transport. -/
theorem prefix_guard_ray_preserves_next_line_value
    {f : Nat -> Nat -> Nat} {r c lo : Nat}
    (hrec : BrouwerRecurrence f)
    (hcr : c <= r)
    (hnextRowLe : r + 1 <= lo)
    (hlopos : 0 < lo)
    (hlohole : Not (B f r c lo))
    (hnextOldHole : Not (B f r c (lo + 1)))
    (hray : PrefixGuardRay f (r + 1) c lo) :
    Not (B f (r + 1) c (lo + 1)) := by
  apply recurrence_prefix_cap_preserves_next_line_value
    hrec hcr hlopos hlohole hnextOldHole
  apply prefix_guard_ray_implies_prefix_cap
    hrec (by omega) hnextRowLe hlopos hray

end ChompLean
