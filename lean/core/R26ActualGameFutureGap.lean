import R25LateBlockerTerminalSplit

set_option autoImplicit false

namespace ChompLean

/-!
R26: the valid replacement for the tempting, but false, direct
`q`-left-return statement.

If `q = f t c` is a large MEX below a still larger unpaid value `z`, the
rightmost-hole principle forces a later row on which `z` is still absent from
the same left prefix `C(-,c)`.  For a future row-start blocker, that later
gap is either still before the freeze, or else row-start propagation gives
an actual host for `z` in the middle band `[c,r)`.

The last theorem specializes the result to the genuine three-row Chomp
encoding `gameF`.
-/

/-- A large emitted value below `z` cannot be followed by uninterrupted
`C(-,c)` coverage of `z` all the way to row `z`. -/
theorem rightmost_hole_forces_future_prefix_gap
    (M : RecurrenceModel) {c t q z : Nat}
    (hct : c < t)
    (hq : M.f t c = q)
    (htq : t < q) (hqz : q < z)
    (hgap : Not (C M.f t c z)) :
    exists x, t < x /\ x < z /\ Not (C M.f x c z) := by
  classical
  by_cases hex : exists x, t < x /\ x < z /\ Not (C M.f x c z)
  · exact hex
  · have hall : forall x, t < x -> x < z -> C M.f x c z := by
      intro x htx hxz
      by_cases hxC : C M.f x c z
      · exact hxC
      · exact False.elim (hex ⟨x, htx, hxz, hxC⟩)
    have hzle : z <= M.f t c :=
      M.rightmost_hole hct (by omega) hgap hall (by rw [hq]; exact htq)
    rw [hq] at hzle
    exact False.elim (by omega)

/-- Exact future-freeze normal form.  The forced later prefix gap is either
at/before the blocker freeze, or it occurs after the freeze and the unique
row-start return is trapped in the middle band `[c,r)` rather than reaching
the desired prefix `<c`. -/
theorem future_rowstart_gap_or_middle_band_return
    (M : RecurrenceModel) {c t q z r : Nat}
    (hct : c < t)
    (hq : M.f t c = q)
    (htq : t < q) (hqz : q < z)
    (hgap : Not (C M.f t c z))
    (hrz : r < z)
    (hstart : M.f z r = z) :
    exists x,
      t < x /\ x < z /\ Not (C M.f x c z) /\
      (x <= r \/
        exists b, c <= b /\ b < r /\ M.f x b = z) := by
  rcases rightmost_hole_forces_future_prefix_gap
      M hct hq htq hqz hgap with ⟨x, htx, hxz, hxgap⟩
  refine ⟨x, htx, hxz, hxgap, ?_⟩
  by_cases hxr : x <= r
  · exact Or.inl hxr
  · have hrx : r < x := by omega
    rcases rowStartPropagation M hstart hrz hrx hxz with
      ⟨b, hbr, hvalue⟩
    have hcb : c <= b := by
      by_cases hle : c <= b
      · exact hle
      · have hbc : b < c := by omega
        exact False.elim (hxgap ⟨b, hbc, hvalue⟩)
    exact Or.inr ⟨b, hcb, hbr, hvalue⟩

/-- Direct R21-facing specialization.  If the second post-entry output is
strictly above the current row but below an unpaid blocker, then the R21
source hole forces the future-gap/middle-band certificate at the very same
prefix column `e+2`. -/
theorem R21_high_lower_loss_forces_blocker_future_gap
    (M : RecurrenceModel) {t e q z r : Nat}
    (het : e + 2 < t)
    (hq : M.f t (e + 2) = q)
    (htq : t < q) (hqz : q < z)
    (hzMissingTwo : Not (B M.f t (e + 2) z))
    (hrz : r < z) (hstart : M.f z r = z) :
    exists x,
      t < x /\ x < z /\ Not (C M.f x (e + 2) z) /\
      (x <= r \/
        exists b, e + 2 <= b /\ b < r /\ M.f x b = z) := by
  have hgap : Not (C M.f t (e + 2) z) := by
    intro hC
    exact hzMissingTwo (Or.inr hC)
  exact future_rowstart_gap_or_middle_band_return
    M het hq htq hqz hgap hrz hstart

/-- The same certificate for the actual noncomputable encoding of
three-row Chomp P-positions. -/
theorem gameF_future_rowstart_gap_or_middle_band_return
    {c t q z r : Nat}
    (hct : c < t)
    (hq : gameF t c = q)
    (htq : t < q) (hqz : q < z)
    (hgap : Not (C gameF t c z))
    (hrz : r < z)
    (hstart : gameF z r = z) :
    exists x,
      t < x /\ x < z /\ Not (C gameF x c z) /\
      (x <= r \/
        exists b, c <= b /\ b < r /\ gameF x b = z) := by
  exact future_rowstart_gap_or_middle_band_return
    gameRecurrenceModel hct hq htq hqz hgap hrz hstart

end ChompLean
