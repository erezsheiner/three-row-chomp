import R151FloorHostOrder

set_option autoImplicit false

namespace ChompLean

/-!
R151F-B: the lag-four boundary case `a = v-4`, attacked from the ladder
side.

`PostExhaustionDeadline`'s hardest instance puts the terminal burn exactly
one row early: `F(v-4, r-1) = v`, with the lag-three preview `F(v-3,H)=v`,
`H<=g`, directly above it.  The all-low tail is then exactly the three
already-given hosts (preview, column-2 rail, column-0 rail), so the only
possible leverage is the completed burn ladder strictly below `v-4`.

This file extracts everything the ladder does force at the boundary:

* the preview row `v-3` is a full high run on the whole suffix `(g, v-3]`
  — not merely on the failed band `(g,r)` as in R136;
* the burn row `v-4` is a full high run on `(g, v-4]` with exactly one
  notch, the target itself at the terminal column `r-1`;
* both diagonals and the `V1` cell of the preview row are pinned at or
  above `v+1`;
* the preview host avoids both rail columns, and the two rows above the
  preview host the target exactly on the rails.

It then records the exact negative: a one-parameter arithmetic frame with
the boundary witness, a complete adjacent ladder landing on `v-4`, the
empty new tail, and forced sub-ladder low rows, satisfying every exported
order/injectivity/ceiling shape.  At the atomic sub-case `r=g+2` the band
interior is empty and the ladder side is structurally vacuous.  The
boundary kill therefore cannot come from first-use order alone; the
surviving obligation is the saturation content of the owner-covered low
cells below the ladder and of the preview cell itself.
-/

/-! ## 1. Full-suffix high run on the preview row

R136's high run needed the loaded interval and stopped at the failed
band `(g,r)`.  With full band saturation the preview host alone pushes
the whole suffix `(g, v-3]` of the preview row strictly above the
target: the target is blocked in the row prefix at `H`, every smaller
value is blocked by owner coverage, and the carry branch is closed by the
owner cutoff.  No failure hypothesis and no freeze hypothesis are used. -/
theorem gameF_preview_suffix_high_run
    {q g H e : Nat}
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hge : g < e)
    (heq : e <= q) :
    q + 4 <= gameF q e := by
  have hnotfirst : Not (e < q /\ gameF (q - 1) e < q) :=
    gameF_noCarry_after_lowerOwnerCutoff (v := q + 3) (s := g)
      (by omega) hge howners
  have hmex := gameF_brouwerRecurrence.2 (q := q) (r := e) heq hnotfirst
  have hsat := gameF_ownerCovered_full_saturation
    (v := q + 3) (g := g) howners (by omega) hge heq
  have hBv : B gameF q e (q + 3) := Or.inr ⟨H, by omega, hpreview⟩
  by_cases hlow : gameF q e < q + 3
  · exact False.elim (hmex.2.1 (hsat (gameF q e) hmex.1 hlow))
  · by_cases heqv : gameF q e = q + 3
    · exact False.elim (hmex.2.1 (by rw [heqv]; exact hBv))
    · omega

/-! ## 2. The burn-row profile: a high run with one notch

On the early witness row the completed ladder blocks the target in the
column channel strictly left of `r-1`, and the witness itself blocks it in
the prefix channel strictly right of `r-1`.  So away from the single notch
`r-1` the whole suffix `(g, a]` of the burn row is strictly above the
target. -/
theorem gameF_earlyTP_burn_row_profile
    {q r g a e : Nat}
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : r <= a)
    (haq : a < q)
    (hearly : gameF a (r - 1) = q + 3)
    (hge : g < e)
    (hea : e <= a)
    (hne : e ≠ r - 1) :
    q + 4 <= gameF a e := by
  have hnotfirst : Not (e < a /\ gameF (a - 1) e < a) :=
    gameF_noCarry_after_lowerOwnerCutoff (v := q + 3) (s := g)
      (by omega) hge howners
  have hmex := gameF_brouwerRecurrence.2 (q := a) (r := e) hea hnotfirst
  have hsat := gameF_ownerCovered_full_saturation
    (v := q + 3) (g := g) howners (by omega) hge hea
  have hBv : B gameF a e (q + 3) := by
    by_cases hcase : e < r - 1
    · rcases gameF_earlyTP_burns_band hrv hstart howners hra haq hearly
        e hge hcase with ⟨w, hew, hwa, hwval⟩
      left
      refine ⟨w, hwa, ?_⟩
      simpa [Nat.min_eq_right (Nat.le_of_lt hew)] using hwval
    · have her : r - 1 < e := by omega
      exact Or.inr ⟨r - 1, her, hearly⟩
  by_cases hlow : gameF a e < q + 3
  · exact False.elim (hmex.2.1 (hsat (gameF a e) hmex.1 hlow))
  · by_cases heqv : gameF a e = q + 3
    · exact False.elim (hmex.2.1 (by rw [heqv]; exact hBv))
    · omega

/-- Diagonal and `V1` pins forced by the two profiles: both row diagonals
and the preview-row `V1` cell sit at or above `v+1`. -/
theorem gameF_earlyTP_high_pins
    {q r g a H : Nat}
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= a)
    (haq : a < q)
    (hearly : gameF a (r - 1) = q + 3)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    q + 4 <= gameF q q /\
      q + 4 <= gameF q (q - 1) /\
      q + 4 <= gameF a a := by
  have hgq : g + 3 <= q := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact gameF_preview_suffix_high_run howners hpreviewLeft hpreview
      (by omega) (Nat.le_refl q)
  · exact gameF_preview_suffix_high_run howners hpreviewLeft hpreview
      (by omega) (by omega)
  · exact gameF_earlyTP_burn_row_profile hrv hstart howners hra haq
      hearly (by omega) (Nat.le_refl a) (by omega)

/-- Below the first burn there is no band host at all: every occurrence
of the target strictly below the burn of the leftmost band column sits at
an owner-covered column.  The ladder therefore pushes the low-host
obligation downward as well as upward: the equality column collides by
same-lower no-repeat, and a higher band column would have to burn later
than the leftmost one by increasing first use. -/
theorem gameF_no_band_host_below_first_burn
    {q r g w s' b : Nat}
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hwv : w < q + 3)
    (hwvalid : g + 1 <= w)
    (hfirst : gameF w (g + 1) = q + 3)
    (hs' : s' < w)
    (hb : g < b)
    (hbs' : b <= s')
    (hbval : gameF s' b = q + 3) :
    False := by
  have hbs : b < s' := by
    rcases Nat.lt_or_ge b s' with h | h
    · exact h
    · have heq : b = s' := by omega
      exact False.elim (disjoint_D_S gameRecurrenceModel
        ⟨s', heq ▸ hbval⟩ ⟨r, hrv, hstart⟩)
  by_cases hb1 : b = g + 1
  · subst hb1
    exact encoding_same_lower_no_repeat game_encodes
      (s := g + 1) (t₁ := s') (t₂ := w) (p := q + 3)
      hbs hs' hwv hbval hfirst
  · have hgb : g + 1 < b := by omega
    have horder := gameF_band_burn_first_use_increases
      (v := q + 3) (r := r) (g := g)
      hrv hstart howners hwv (by omega) (by omega) hgb hwvalid hbs'
      hfirst hbval
    omega

/-- The preview host avoids both rail columns: the column-0 and column-2
rails already carry `q+1` and `q+2` there, not the target. -/
theorem gameF_preview_host_not_rail
    {q H : Nat}
    (hq2 : 2 <= q)
    (hpreview : gameF q H = q + 3) :
    H ≠ 0 /\ H ≠ 2 := by
  constructor
  · intro h0
    rw [h0] at hpreview
    have hc := gameF_col0 q
    rw [hc] at hpreview
    omega
  · intro h2
    rw [h2] at hpreview
    have hc := gameF_col2_rail hq2
    rw [hc] at hpreview
    omega

/-! ## 3. The boundary package `a = v-4` -/

/-- Everything the ladder side forces at the boundary, in one statement:
the complete ordered burn strictly below `v-4`, the notched high-run
profile of row `v-4`, the full-suffix high run of row `v-3`, the exact
rail hosts of rows `v-2` and `v-1`, and the non-rail preview host.  The
all-low tail of the normal form is exactly the three displayed hosts, so
no clause of this package is left to attack on the tail side. -/
theorem gameF_lag4_boundary_package
    {q r g H : Nat}
    (hq2 : 2 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (_hfailure : g + 1 < r)
    (hra : r <= q - 1)
    (hearly : gameF (q - 1) (r - 1) = q + 3)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    (forall e, g < e -> e < r - 1 ->
      exists w, e < w /\ w < q - 1 /\ gameF w e = q + 3) /\
    (forall e, g < e -> e <= q - 1 -> e ≠ r - 1 ->
      q + 4 <= gameF (q - 1) e) /\
    (forall e, g < e -> e <= q -> q + 4 <= gameF q e) /\
    gameF (q + 1) 2 = q + 3 /\
    gameF (q + 2) 0 = q + 3 /\
    H ≠ 0 /\ H ≠ 2 := by
  have haq : q - 1 < q := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gameF_earlyTP_burns_band hrv hstart howners hra haq hearly
  · intro e hge hea hne
    exact gameF_earlyTP_burn_row_profile hrv hstart howners hra haq
      hearly hge hea hne
  · intro e hge heq
    exact gameF_preview_suffix_high_run howners hpreviewLeft hpreview
      hge heq
  · have hc := gameF_col2_rail (q := q + 1) (by omega)
    omega
  · have hc := gameF_col0 (q + 2)
    omega
  · exact gameF_preview_host_not_rail hq2 hpreview

/-! ## 4. Boundary order-interface counterframe

The same `v=10k, g=7k, r=8k` geometry with the terminal burn moved to the
boundary row `a=v-4`: the ladder is shifted up (`w(e)=e+2k-3`), lands
exactly on the boundary, and leaves `k-3` forced sub-ladder low rows
between the freeze row of the frame and the first burn.  The new tail
above the witness is empty: it consists of exactly the three given hosts.
Every exported order/injectivity/ceiling shape of Sections 1-3 is
satisfied, so the boundary case cannot be refuted from the ladder-side
order bank; the surviving content is the saturation of the sub-ladder low
cells and of the preview cell. -/

def r151fbA (k : Nat) : Nat := 10 * k - 4
def r151fbBurnRow (k e : Nat) : Nat := e + (2 * k - 3)

/-- The boundary frame: a strict first failure whose terminal burn row is
exactly one below the lag-three row. -/
theorem r151fb_boundary_frame {k : Nat} (hk : 4 <= k) :
    r151fG k + 1 < r151fR k /\
      r151fR k <= r151fbA k /\
      r151fbA k + 1 = r151fQ k /\
      r151fQ k + 3 = r151fV k /\
      r151fH k <= r151fG k /\
      r151fR k - (r151fG k + 1) = k - 1 := by
  simp [r151fG, r151fR, r151fbA, r151fQ, r151fV, r151fH]
  omega

/-- The shifted ladder: adjacent, strictly inside `(r, a)`, consuming
each band column strictly above itself. -/
theorem r151fb_burn_ladder {k e : Nat} (hk : 4 <= k)
    (he0 : r151fG k < e) (he1 : e < r151fR k - 1) :
    e < r151fbBurnRow k e /\
      r151fR k < r151fbBurnRow k e /\
      r151fbBurnRow k e < r151fbA k /\
      r151fbBurnRow k (e + 1) = r151fbBurnRow k e + 1 := by
  simp [r151fG, r151fR, r151fbA, r151fbBurnRow] at he0 he1 ⊢
  omega

/-- The terminal burn lands exactly on the boundary row `v-4`. -/
theorem r151fb_terminal_lands_on_boundary {k : Nat} (hk : 4 <= k) :
    r151fbBurnRow k (r151fR k - 1) = r151fbA k /\
      r151fQ k - r151fbA k = 1 := by
  simp [r151fR, r151fbA, r151fQ, r151fbBurnRow]
  omega

/-- The new tail is empty: the rows strictly between the boundary witness
and the blocker are exactly the lag-three preview row and the two rail
rows, with exactly the three given host columns. -/
theorem r151fb_empty_new_tail {k s : Nat} (hk : 4 <= k)
    (hs0 : r151fbA k < s) (hs1 : s < r151fV k) :
    (s = r151fQ k /\ r151fLowCol k s = r151fH k) \/
    (s = r151fQ k + 1 /\ r151fLowCol k s = 2) \/
    (s = r151fQ k + 2 /\ r151fLowCol k s = 0) := by
  simp [r151fbA, r151fV, r151fQ, r151fH, r151fLowCol] at hs0 hs1 ⊢
  omega

/-- The shifted ladder forces `k-3` sub-ladder low rows: every row
strictly between the frame's freeze row and the first burn is hosted at
an owner-covered column, disjoint from the three tail columns, with the
cell ceiling intact. -/
theorem r151fb_subladder_low_rows {k s : Nat} (hk : 4 <= k)
    (hs0 : r151fR k < s) (hs1 : s < r151fbBurnRow k (r151fG k + 1)) :
    r151fLowCol k s <= r151fG k /\
      r151fLowCol k s <= s /\
      r151fV k <= s + r151fLowCol k s + 1 /\
      2 * k + 2 <= r151fLowCol k s := by
  simp [r151fR, r151fG, r151fV, r151fbBurnRow, r151fLowCol] at hs0 hs1 ⊢
  omega

/-- Count of the forced sub-ladder low rows: `k-3`, unbounded. -/
theorem r151fb_subladder_count {k : Nat} (hk : 4 <= k) :
    r151fbBurnRow k (r151fG k + 1) - r151fR k - 1 = k - 3 := by
  simp [r151fbBurnRow, r151fG, r151fR]
  omega

/-- At the atomic sub-case `r=g+2` the band interior is empty: the ladder
side of the boundary attack is structurally vacuous there. -/
theorem r151f_atomic_band_empty {g r e : Nat}
    (hatomic : r = g + 2) :
    Not (g < e /\ e < r - 1) := by
  omega

#print axioms gameF_preview_suffix_high_run
#print axioms gameF_earlyTP_burn_row_profile
#print axioms gameF_earlyTP_high_pins
#print axioms gameF_no_band_host_below_first_burn
#print axioms gameF_preview_host_not_rail
#print axioms gameF_lag4_boundary_package
#print axioms r151fb_boundary_frame
#print axioms r151fb_burn_ladder
#print axioms r151fb_terminal_lands_on_boundary
#print axioms r151fb_empty_new_tail
#print axioms r151fb_subladder_low_rows
#print axioms r151fb_subladder_count
#print axioms r151f_atomic_band_empty

end ChompLean
