import R151FloorHostOrder

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight terminal-sibling audit

The proposed adaptive atom asked whether a terminal-predecessor burn could
force a low sibling in the same column on the lag-three preview row.  Under
the R151 lower-owner hypothesis the recurrence forces the opposite.

Once `v` occurs in a band column, that old occurrence blocks `v` in every
later MEX cell of the same column.  Owner coverage blocks every positive
value below `v`, and the owner cutoff excludes the carry branch.  Hence the
column stays strictly above `v` until row `v`.
-/

/-- A burned post-cutoff column stays strictly above the burned target on
every later pre-birth row.  This is independent of a preview host and even
of the target's eventual freeze. -/
theorem gameF_burned_band_column_stays_above_target
    {v g a e s : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (hge : g < e)
    (hea : e <= a)
    (has : a < s)
    (hsv : s < v)
    (hburn : gameF a e = v) :
    v < gameF s e := by
  have hes : e <= s := by omega
  have hnotCarry : Not (e < s /\ gameF (s - 1) e < s) :=
    gameF_noCarry_after_lowerOwnerCutoff
      (v := v) (s := g) (q := s) (e := e) hsv hge howners
  have hmex := gameF_brouwerRecurrence.2
    (q := s) (r := e) hes hnotCarry
  have hsat := gameF_ownerCovered_full_saturation
    (v := v) (g := g) (t := s) (e := e) howners hsv hge hes
  have hBv : B gameF s e v := by
    left
    refine ⟨a, has, ?_⟩
    simpa [Nat.min_eq_right hea] using hburn
  by_cases hlt : gameF s e < v
  · exact False.elim
      (hmex.2.1 (hsat (gameF s e) hmex.1 hlt))
  · by_cases heq : gameF s e = v
    · exact False.elim (hmex.2.1 (by rw [heq]; exact hBv))
    · omega

/-- Exact lag-eight indexing in target coordinates.  If the target is `v`,
then the lag-eight burn row is `v-8`; the lag-three preview row is `v-3`.
The terminal-predecessor cell on that preview row is at least `v+1`, not a
low sibling. -/
theorem gameF_lag8_burn_forces_preview_predecessor_high
    {v r g : Nat}
    (hv : 11 <= v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v) :
    v + 1 <= gameF (v - 3) (r - 1) := by
  have hhigh := gameF_burned_band_column_stays_above_target
    (v := v) (g := g) (a := v - 8) (e := r - 1) (s := v - 3)
    howners (by omega) (by omega) (by omega) (by omega) hburn
  omega

/-- R151 preview coordinates use `v=q+3`; consequently lag eight is
`a=v-8=q-5` (not `q-4`). -/
theorem gameF_q_lag8_burn_forces_terminal_preview_high
    {q r g : Nat}
    (hq : 8 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3) :
    q + 4 <= gameF q (r - 1) := by
  have hhigh := gameF_burned_band_column_stays_above_target
    (v := q + 3) (g := g) (a := q - 5) (e := r - 1) (s := q)
    howners (by omega) (by omega) (by omega) (by omega) hburn
  omega

/-- Thus the candidate weak sibling bound `F(q,r-1)<=v` is incompatible
with the actual R151 owner-covered lag-eight frame. -/
theorem gameF_q_lag8_terminal_low_sibling_impossible
    {q r g : Nat}
    (hq : 8 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hsibling : gameF q (r - 1) <= q + 3) :
    False := by
  have hhigh := gameF_q_lag8_burn_forces_terminal_preview_high
    hq howners hfailure hra hburn
  omega

/-- The genuine `v-3` sibling forced by owner coverage is already absorbed
strictly on the left.  It is either a diagonal owner at or before `g`, or
a future blocker with freeze at or before `g` and a propagated host on the
lag-eight burn row strictly left of that freeze.  In particular, the
recurrence provides no reason for this sibling to open at `r-1`. -/
theorem gameF_lag8_preview_sibling_left_owner_normal_form
    {v r g : Nat}
    (hv : 11 <= v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8) :
    (exists d, d <= g /\ gameF d d = v - 3) \/
    (exists rk b,
      rk <= g /\ b < rk /\ rk < v - 3 /\
      gameF (v - 3) rk = v - 3 /\
      gameF (v - 8) b = v - 3) := by
  have hkpos : 0 < v - 3 := by omega
  have hkv : v - 3 < v := by omega
  rcases howners (v - 3) hkpos hkv with
      ⟨d, hdg, hdiag⟩ | ⟨rk, hrkg, hrkk, hstart⟩
  · exact Or.inl ⟨d, hdg, hdiag⟩
  · have hrka : rk < v - 8 := by omega
    have hak : v - 8 < v - 3 := by omega
    rcases rowStartPropagation gameRecurrenceModel hstart hrkk hrka hak with
      ⟨b, hbrk, hbval⟩
    exact Or.inr ⟨rk, b, hrkg, hbrk, hrkk, hstart, by simpa using hbval⟩

#print axioms gameF_burned_band_column_stays_above_target
#print axioms gameF_lag8_burn_forces_preview_predecessor_high
#print axioms gameF_q_lag8_burn_forces_terminal_preview_high
#print axioms gameF_q_lag8_terminal_low_sibling_impossible
#print axioms gameF_lag8_preview_sibling_left_owner_normal_form

end ChompLean
