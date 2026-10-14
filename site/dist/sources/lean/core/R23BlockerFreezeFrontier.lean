import R22L3PastRangeEscape

set_option autoImplicit false

namespace ChompLean

/-!
R23: exact row-start/blocker frontier for a rescue source.

A blocker value `z` is represented by a row start `f z r = z`; call `r`
its freeze column.  The recurrence gives two complementary transports:

* before row `z`, `rowStartPropagation` puts `z` in a still earlier column;
* from row `z` onward, `constant_from` keeps `z` in column `r`.

Consequently a blocker whose freeze column is strictly left of a source
cannot be missing from that source.  If it is missing and is not the value
emitted by the source cell, its freeze column is strictly to the right.
This is the Chomp-specific replacement for the unresolved blocker branch of
`NO-LOWER-NEW-LOSS`.
-/

/-- A row-start value whose freeze column lies strictly left of a source is
already in that source, for every relative order of the current row `t` and
the blocker value `z`. -/
theorem rowstart_freeze_lt_source_is_covered
    (M : RecurrenceModel) {t c z r : Nat}
    (hct : c < t)
    (hrz : r < z) (hstart : M.f z r = z)
    (hrc : r < c) :
    B M.f t c z := by
  right
  by_cases htz : t < z
  · rcases rowStartPropagation M hstart hrz (by omega) htz with
      ⟨b, hbr, hvalue⟩
    exact ⟨b, by omega, hvalue⟩
  · have hzt : z <= t := Nat.le_of_not_gt htz
    have hsmall : M.f z r < z + 1 := by
      rw [hstart]
      omega
    have hconst := constant_from M hrz hsmall (t - z)
    have hsum : z + (t - z) = t := by omega
    have hcurrent : M.f t r = z := by
      simpa [hsum, hstart] using hconst
    exact ⟨r, hrc, hcurrent⟩

/-- At the boundary itself, a row-start value is covered one source later.
This includes the case where the current row has reached the blocker row:
then the boundary cell literally emits the blocker. -/
theorem rowstart_freeze_le_source_closes_next
    (M : RecurrenceModel) {t c z r : Nat}
    (hct : c < t)
    (hrz : r < z) (hstart : M.f z r = z)
    (hrc : r <= c) :
    C M.f t (c + 1) z := by
  by_cases htz : t < z
  · rcases rowStartPropagation M hstart hrz (by omega) htz with
      ⟨b, hbr, hvalue⟩
    exact ⟨b, by omega, hvalue⟩
  · have hzt : z <= t := Nat.le_of_not_gt htz
    have hsmall : M.f z r < z + 1 := by
      rw [hstart]
      omega
    have hconst := constant_from M hrz hsmall (t - z)
    have hsum : z + (t - z) = t := by omega
    have hcurrent : M.f t r = z := by
      simpa [hsum, hstart] using hconst
    exact ⟨r, by omega, hcurrent⟩

/-- Exact blocker frontier: absence from source `c` forces the freeze column
to be at or to the right of `c`. -/
theorem missing_rowstart_forces_freeze_at_or_right
    (M : RecurrenceModel) {t c z r : Nat}
    (hct : c < t)
    (hrz : r < z) (hstart : M.f z r = z)
    (hmissing : Not (B M.f t c z)) :
    c <= r := by
  by_cases hcr : c <= r
  · exact hcr
  · have hrc : r < c := by omega
    exact False.elim (hmissing
      (rowstart_freeze_lt_source_is_covered M hct hrz hstart hrc))

/-- Strong form of the frontier.  If the blocker is absent from the source
and the source cell does not emit it, then the freeze column is strictly to
the right of that cell. -/
theorem missing_unemitted_rowstart_forces_freeze_right
    (M : RecurrenceModel) {t c z r : Nat}
    (hct : c < t)
    (hrz : r < z) (hstart : M.f z r = z)
    (hmissing : Not (B M.f t c z))
    (hnotEmitted : M.f t c ≠ z) :
    c < r := by
  have hcr := missing_rowstart_forces_freeze_at_or_right
    M hct hrz hstart hmissing
  by_cases hstrict : c < r
  · exact hstrict
  · have hrc : r = c := by omega
    subst r
    by_cases htz : t < z
    · have hcovered : C M.f t c z :=
        rowStartPropagation M hstart hrz hct htz
      exact False.elim (hmissing (Or.inr hcovered))
    · have hzt : z <= t := Nat.le_of_not_gt htz
      have hsmall : M.f z c < z + 1 := by
        rw [hstart]
        omega
      have hconst := constant_from M hrz hsmall (t - z)
      have hsum : z + (t - z) = t := by omega
      have hcurrent : M.f t c = z := by
        simpa [hsum, hstart] using hconst
      exact False.elim (hnotEmitted hcurrent)

/-- A compact trichotomy useful at a backstop: a blocker is already in the
source, is emitted by the boundary cell, or has a genuinely later freeze
column. -/
theorem rowstart_source_or_boundary_emission_or_late_freeze
    (M : RecurrenceModel) {t c z r : Nat}
    (hct : c < t)
    (hrz : r < z) (hstart : M.f z r = z) :
    B M.f t c z \/ M.f t c = z \/ c < r := by
  by_cases hrc : r < c
  · exact Or.inl
      (rowstart_freeze_lt_source_is_covered M hct hrz hstart hrc)
  by_cases hcr : c < r
  · exact Or.inr (Or.inr hcr)
  have hrcEq : r = c := by omega
  subst r
  by_cases htz : t < z
  · exact Or.inl (Or.inr (rowStartPropagation M hstart hrz hct htz))
  · have hzt : z <= t := Nat.le_of_not_gt htz
    have hsmall : M.f z c < z + 1 := by
      rw [hstart]
      omega
    have hconst := constant_from M hrz hsmall (t - z)
    have hsum : z + (t - z) = t := by omega
    have hcurrent : M.f t c = z := by
      simpa [hsum, hstart] using hconst
    exact Or.inr (Or.inl hcurrent)

/-- Combine the R21 lower-new-loss obstruction with the blocker frontier.
For every rescue length `L >= 3`, an unserved blocker whose freeze column is
strictly before the backstop causes no mixed-pair failure: the fresh lower
loss persists in the current-row prefix, while the blocker has already been
transported there by row-start chronology. -/
theorem rescue_unserved_early_blocker_pair_reaches_backstop
    (M : RecurrenceModel) {e L u z r : Nat}
    (hL : 3 <= L)
    (hmexEntry :
      IsMex (B M.f (e + L + 3) e) (M.f (e + L + 3) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f (e + L + 3) e y) ->
        Not (B M.f (e + L + 3) e z) -> y = z)
    (hmexOne :
      IsMex (B M.f (e + L + 3) (e + 1))
        (M.f (e + L + 3) (e + 1)))
    (hmexTwo :
      IsMex (B M.f (e + L + 3) (e + 2))
        (M.f (e + L + 3) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + L + 3) e x ->
          Not (B M.f (e + L + 3) (e + 1) x) ->
        B M.f (e + L + 3) e y ->
          Not (B M.f (e + L + 3) (e + 1) y) ->
        B M.f (e + L + 3) e z ->
          Not (B M.f (e + L + 3) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + L + 3) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + L + 3) (e + 2) z))
    (hNotServed : M.f (e + L + 3) (e + 2) ≠ z)
    (hrz : r < z) (hstart : M.f z r = z)
    (hrBeforeBackstop : r < e + L) :
    let q := M.f (e + L + 3) (e + 2)
    0 < q /\ q < z /\
      B M.f (e + L + 3) (e + 1) q /\
      Not (B M.f (e + L + 3) (e + 2) q) /\
      B M.f (e + L + 3) (e + L) q /\
      B M.f (e + L + 3) (e + L) z := by
  let q := M.f (e + L + 3) (e + 2)
  have hobs := unserved_persistent_hole_forces_lower_new_loss
    hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
    hz hzu hzMissingOne hzMissingTwo hNotServed
  have hqFinal : B M.f (e + L + 3) (e + L) q := by
    exact fresh_emission_persists_in_all_later_sources
      (f := M.f) (t := e + L + 3) (e := e + 2) (z := q) rfl (by omega)
  have hzFinal : B M.f (e + L + 3) (e + L) z :=
    rowstart_freeze_lt_source_is_covered
      M (by omega) hrz hstart hrBeforeBackstop
  exact ⟨hobs.1, hobs.2.1, hobs.2.2.1, hobs.2.2.2,
    hqFinal, hzFinal⟩

/-- Exact `L=3` residual after R21.  If an unserved blocker is still absent
at the backstop, then either its freeze column is strictly after the
backstop, or it freezes exactly at the backstop and the backstop cell emits
it.  In the latter case the blocker is necessarily no larger than the
current-row index. -/
theorem l3_unserved_blocker_missing_backstop_normal_form
    (M : RecurrenceModel) {e z r : Nat}
    (hrz : r < z) (hstart : M.f z r = z)
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (hNotServed : M.f (e + 6) (e + 2) ≠ z)
    (hzMissingFinal : Not (B M.f (e + 6) (e + 3) z)) :
    e + 3 < r \/
      (r = e + 3 /\ z <= e + 6 /\ M.f (e + 6) (e + 3) = z) := by
  have hafterSecond : e + 2 < r :=
    missing_unemitted_rowstart_forces_freeze_right
      M (by omega) hrz hstart hzMissingTwo hNotServed
  have hatOrAfterFinal : e + 3 <= r :=
    missing_rowstart_forces_freeze_at_or_right
      M (by omega) hrz hstart hzMissingFinal
  by_cases hlate : e + 3 < r
  · exact Or.inl hlate
  · have hr : r = e + 3 := by omega
    subst r
    have hzt : z <= e + 6 := by
      by_cases hle : z <= e + 6
      · exact hle
      · have htz : e + 6 < z := by omega
        have hcovered : C M.f (e + 6) (e + 3) z :=
          rowStartPropagation M hstart hrz (by omega) htz
        exact False.elim (hzMissingFinal (Or.inr hcovered))
    have hsmall : M.f z (e + 3) < z + 1 := by
      rw [hstart]
      omega
    have hconst := constant_from M hrz hsmall (e + 6 - z)
    have hsum : z + (e + 6 - z) = e + 6 := by omega
    have hemit : M.f (e + 6) (e + 3) = z := by
      simpa [hsum, hstart] using hconst
    exact Or.inr ⟨rfl, hzt, hemit⟩

/-- On the large-value branch `t<z` relevant to the observed blocker
witness, the boundary-emission alternative disappears: a blocker missing
from the `L=3` backstop must freeze strictly after that backstop. -/
theorem l3_large_unserved_blocker_missing_backstop_forces_late_freeze
    (M : RecurrenceModel) {e z r : Nat}
    (hrz : r < z) (hstart : M.f z r = z)
    (htz : e + 6 < z)
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (hNotServed : M.f (e + 6) (e + 2) ≠ z)
    (hzMissingFinal : Not (B M.f (e + 6) (e + 3) z)) :
    e + 3 < r := by
  rcases l3_unserved_blocker_missing_backstop_normal_form
      M hrz hstart hzMissingTwo hNotServed hzMissingFinal with
      hlate | ⟨_, hzt, _⟩
  · exact hlate
  · omega

end ChompLean
