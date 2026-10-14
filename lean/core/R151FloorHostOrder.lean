import R137UpperRailTerminalTimingReduction

set_option autoImplicit false

namespace ChompLean

/-!
R151F: first/last-use host order inside a failed upper-rail band.

Fix a blocker `v` with actual freeze `F(v,r)=v` and owner coverage through
`g`.  The failed band is the open column interval `(g,r)`; it is nonempty
exactly when the upper rail fails (`g+1<r`).

The new point is that inside the band the recurrence itself forces a
complete first-use order.  Owner coverage saturates every band cell at all
positive values below `v`, including the values strictly above the cell's
own row (diagonal owners enter the fixed-`R` channel; already frozen
row-starts enter the prefix channel through `rowStartPropagation`).  A band
cell that is not blocked at `v` therefore has MEX exactly `v`.  Fixed-row
injectivity then rules out skipping: a band host at column `c` forces every
band column strictly between `g` and `c` to have been consumed strictly
below its own row.

Consequences under the R137 first-failure frame:

* the early terminal-predecessor witness at `(a,r-1)` forces the whole
  band `(g,r-1)` to be burned strictly below `a`, in strictly increasing
  first-use order;
* every remaining pre-freeze row `s in (a,v)` must host the target at an
  owner-covered column `b<=g`.

This is a genuine first/last-use law, not a cardinality statement.  It does
not close `FF-TP-NO-EARLY`; the exact residual is packaged below as
`PostExhaustionDeadline`, and the terminal section records an all-index
arithmetic interface frame satisfying every exported order/injectivity
consequence with an unboundedly early terminal burn.
-/

/-! ## 1. Full band saturation from owner coverage

`lowerOwnerCoveredBy_source_saturation_on_earlier_row` (R136) saturates a
post-cutoff cell at all values up to its own row.  The extension to all
values below the blocker is exact: a value above the row is either a range
value whose diagonal owner sits at a column `<=g`, hence strictly left of
the band cell, or an already frozen row-start whose propagation host on the
current row sits strictly left of its own freeze column `<=g`. -/
theorem gameF_ownerCovered_full_saturation
    {v g t e : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (htv : t < v)
    (hge : g < e)
    (het : e <= t) :
    forall k, 0 < k -> k < v -> B gameF t e k := by
  intro k hkpos hkv
  by_cases hkt : k <= t
  · exact lowerOwnerCoveredBy_source_saturation_on_earlier_row
      (v := v) (s := g) (q := t) (e := e) htv hge het howners k hkpos hkt
  · have htk : t < k := Nat.lt_of_not_ge hkt
    rcases howners k hkpos hkv with
        ⟨a, hag, hdiag⟩ | ⟨rk, hrkg, hrkk, hstartk⟩
    · left
      refine ⟨a, by omega, ?_⟩
      have hae : a <= e := by omega
      simpa [Nat.min_eq_left hae] using hdiag
    · right
      have hC := rowStartPropagation gameRecurrenceModel
        (p := k) (r := rk) hstartk hrkk (q := t) (by omega) htk
      rcases hC with ⟨b, hbrk, hbval⟩
      change gameF t b = k at hbval
      exact ⟨b, by omega, hbval⟩

/-! ## 2. The band-cell trichotomy

A pre-freeze band cell can only do one of three things about the target:
see it in its own row prefix, see it in its own column history, or emit it
as the current MEX.  There is no fourth branch: the carry branch is closed
by the owner cutoff, low MEX outputs are closed by full saturation, and
high MEX outputs are closed because the missing target itself caps the
MEX.  The diagonal reading of the fixed-`R` channel is impossible because
the target is a row-start value (`disjoint_D_S`). -/
theorem gameF_band_cell_trichotomy
    {v r g t e : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (htv : t < v)
    (hge : g < e)
    (het : e <= t) :
    (exists b, b < e /\ gameF t b = v) \/
    (exists w, e < w /\ w < t /\ gameF w e = v) \/
    gameF t e = v := by
  have hnotfirst : Not (e < t /\ gameF (t - 1) e < t) :=
    gameF_noCarry_after_lowerOwnerCutoff (v := v) (s := g) htv hge howners
  have hmex := gameF_brouwerRecurrence.2 (q := t) (r := e) het hnotfirst
  by_cases hBv : B gameF t e v
  · cases hBv with
    | inl hR =>
        rcases hR with ⟨w, hwt, hwval⟩
        by_cases hwe : w <= e
        · have hdiag : gameF w w = v := by
            simpa [Nat.min_eq_left hwe] using hwval
          exact False.elim (disjoint_D_S gameRecurrenceModel
            ⟨w, hdiag⟩ ⟨r, hrv, hstart⟩)
        · have hew : e < w := Nat.lt_of_not_ge hwe
          have hcol : gameF w e = v := by
            simpa [Nat.min_eq_right (Nat.le_of_lt hew)] using hwval
          exact Or.inr (Or.inl ⟨w, hew, hwt, hcol⟩)
    | inr hC =>
        rcases hC with ⟨b, hbe, hbval⟩
        exact Or.inl ⟨b, hbe, hbval⟩
  · have hsat := gameF_ownerCovered_full_saturation
      (v := v) (g := g) howners htv hge het
    have hpos : 0 < gameF t e := hmex.1
    by_cases hlt : gameF t e < v
    · exact False.elim (hmex.2.1 (hsat (gameF t e) hpos hlt))
    · by_cases hgt : v < gameF t e
      · exact False.elim (hBv (hmex.2.2 v (by omega) hgt))
      · have hout : gameF t e = v := by omega
        exact Or.inr (Or.inr hout)

/-! ## 3. The no-skip law

A band host cannot jump over an unconsumed band column.  If row `t` hosts
the target at band column `c`, then every band column `e<c` was consumed
strictly below `t`: the prefix branch and the emission branch of the
trichotomy at `(t,e)` both collide with the row-`t` host by fixed-row
injectivity, leaving only the column-history branch.  Band first use is
therefore adjacent and strictly left-to-right. -/
theorem gameF_band_host_no_skip
    {v r g t c e : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (htv : t < v)
    (hhost : gameF t c = v)
    (hct : c <= t)
    (hge : g < e)
    (hec : e < c) :
    exists w, e < w /\ w < t /\ gameF w e = v := by
  rcases gameF_band_cell_trichotomy (v := v) (r := r) (g := g)
      hrv hstart howners htv hge (by omega) with
    ⟨b, hbe, hbval⟩ | hburn | hnow
  · have hbc : b = c := gameRecurrenceModel.fixed_q_injective
      (by omega) hct (hbval.trans hhost.symm)
    omega
  · exact hburn
  · have hec' : e = c := gameRecurrenceModel.fixed_q_injective
      (by omega) hct (hnow.trans hhost.symm)
    omega

/-- Band first use is strictly increasing: of two band consumptions, the
one at the smaller column happens strictly earlier.  Uniqueness of the
lower consumption row is `encoding_same_lower_no_repeat`. -/
theorem gameF_band_burn_first_use_increases
    {v r g e₁ e₂ w₁ w₂ : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hw₁ : w₁ < v)
    (hw₂ : w₂ < v)
    (hge₁ : g < e₁)
    (he₁₂ : e₁ < e₂)
    (he₁w : e₁ <= w₁)
    (he₂w : e₂ <= w₂)
    (hb₁ : gameF w₁ e₁ = v)
    (hb₂ : gameF w₂ e₂ = v) :
    w₁ < w₂ := by
  have he₁w₁ : e₁ < w₁ := by
    rcases Nat.lt_or_ge e₁ w₁ with h | h
    · exact h
    · have heq : e₁ = w₁ := by omega
      exact False.elim (disjoint_D_S gameRecurrenceModel
        ⟨w₁, heq ▸ hb₁⟩ ⟨r, hrv, hstart⟩)
  rcases gameF_band_host_no_skip (v := v) (r := r) (g := g)
      hrv hstart howners hw₂ hb₂ he₂w hge₁ he₁₂ with
    ⟨w', hw'e, hw'w₂, hw'val⟩
  by_cases hww : w₁ = w'
  · omega
  · rcases Nat.lt_or_ge w₁ w' with hlt | hge'
    · exact False.elim (encoding_same_lower_no_repeat game_encodes
        (s := e₁) (t₁ := w₁) (t₂ := w') (p := v)
        he₁w₁ hlt (by omega) hb₁ hw'val)
    · have hlt' : w' < w₁ := by omega
      exact False.elim (encoding_same_lower_no_repeat game_encodes
        (s := e₁) (t₁ := w') (t₂ := w₁) (p := v)
        hw'e hlt' (by omega) hw'val hb₁)

/-! ## 4. First-failure consequences

From here on the frame is R137's strict first-failure frame at `v=q+3`. -/

/-- An early terminal-predecessor witness burns the whole band strictly
below itself, in particular strictly below the lag-three row. -/
theorem gameF_earlyTP_burns_band
    {q r g a : Nat}
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : r <= a)
    (haq : a < q)
    (hearly : gameF a (r - 1) = q + 3) :
    forall e, g < e -> e < r - 1 ->
      exists w, e < w /\ w < a /\ gameF w e = q + 3 := by
  intro e hge her
  exact gameF_band_host_no_skip (v := q + 3) (r := r) (g := g)
    hrv hstart howners (by omega) hearly (by omega) hge her

/-- After an early terminal burn the band is exhausted, so every remaining
pre-freeze row must host the target at an owner-covered column `b<=g`.
The propagation host is strictly left of the freeze; the terminal column
`r-1` is excluded by same-lower no-repeat against the witness row, and any
interior band column is excluded against its own earlier burn row. -/
theorem gameF_earlyTP_forces_low_tail
    {q r g a : Nat}
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (_hfailure : g + 1 < r)
    (hra : r <= a)
    (haq : a < q)
    (hearly : gameF a (r - 1) = q + 3) :
    forall s, a < s -> s < q + 3 ->
      exists b, b <= g /\ gameF s b = q + 3 := by
  intro s has hsv
  have hC := rowStartPropagation gameRecurrenceModel
    (p := q + 3) (r := r) hstart hrv (q := s) (by omega) hsv
  rcases hC with ⟨b, hbr, hbval⟩
  change gameF s b = q + 3 at hbval
  by_cases hbg : b <= g
  · exact ⟨b, hbg, hbval⟩
  · exfalso
    have hgb : g < b := Nat.lt_of_not_ge hbg
    by_cases hbr1 : b = r - 1
    · subst hbr1
      exact encoding_same_lower_no_repeat game_encodes
        (s := r - 1) (t₁ := a) (t₂ := s) (p := q + 3)
        (by omega) has hsv hearly hbval
    · have hblt : b < r - 1 := by omega
      rcases gameF_earlyTP_burns_band hrv hstart howners hra haq hearly
        b hgb hblt with ⟨w, hwb, hwa, hwval⟩
      exact encoding_same_lower_no_repeat game_encodes
        (s := b) (t₁ := w) (t₂ := s) (p := q + 3)
        hwb (by omega) hsv hwval hbval

/-- Complete first-failure normal form.  Either the upper rail holds, or
there is a terminal-predecessor witness row `a` with the full ordered burn
ladder strictly below it and an all-low host tail strictly above it. -/
theorem gameF_firstFailure_burn_ladder_normal_form
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    exists a, r <= a /\ a < q /\ gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_forces_early_terminal_sighting
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hearly⟩
  exact ⟨a, hra, haq, hearly,
    gameF_earlyTP_burns_band hrv hstart howners hra haq hearly,
    gameF_earlyTP_forces_low_tail hrv hstart howners hfailure hra haq
      hearly⟩

/-! ## 5. The exact residual -/

/-- The post-exhaustion deadline.  After a full ordered band burn ending at
an early terminal-predecessor row, the remaining pre-freeze rows would all
have to host the target at owner-covered columns; the deadline law asserts
that this tail cannot exist.  By the normal form above this is exactly what
separates a first upper-rail failure from the real game. -/
def PostExhaustionDeadline : Prop :=
  forall q r g H a : Nat,
    1 <= q ->
    r < q + 3 ->
    gameF (q + 3) r = q + 3 ->
    LowerOwnerCoveredBy (q + 3) g ->
    g + 1 < r ->
    2 < g + 1 ->
    H <= q -> H <= g -> gameF q H = q + 3 ->
    r <= a -> a < q ->
    gameF a (r - 1) = q + 3 ->
    (forall e, g < e -> e < r - 1 ->
      exists w, e < w /\ w < a /\ gameF w e = q + 3) ->
    (forall s, a < s -> s < q + 3 ->
      exists b, b <= g /\ gameF s b = q + 3) ->
    False

/-- The deadline closes the first failed rail.  This is the exact closure
interface: `PostExhaustionDeadline` implies `AssignmentUpper` on the R137
first-failure frame. -/
theorem gameF_upperRail_of_postExhaustionDeadline
    (hdeadline : PostExhaustionDeadline)
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    r <= g + 1 := by
  by_cases hfailure : g + 1 < r
  · exfalso
    rcases gameF_firstFailure_burn_ladder_normal_form
        hq hrv hstart howners hfailure hinterior hpreviewLe
        hpreviewLeft hpreview with ⟨a, hra, haq, hearly, hburn, htail⟩
    exact hdeadline q r g H a hq hrv hstart howners hfailure hinterior
      hpreviewLe hpreviewLeft hpreview hra haq hearly hburn htail
  · omega

/-! ## 6. All-index order-interface counterframe

The following arithmetic family shows that the exported order consequences
above — ordered adjacent burn ladder, all-low tail, rail endpoints, host
injectivity, cell ceiling, and the R148-style scalar interfaces — do not
by themselves refute an unboundedly early terminal burn.  It is an
interface frame in the R151U genre, not a recurrence table: its force is
that any proof of `PostExhaustionDeadline` must consume information beyond
these exported shapes (the actual saturation content of the low-tail host
cells). -/

def r151fV (k : Nat) : Nat := 10 * k
def r151fQ (k : Nat) : Nat := 10 * k - 3
def r151fG (k : Nat) : Nat := 7 * k
def r151fR (k : Nat) : Nat := 8 * k
def r151fA (k : Nat) : Nat := 9 * k - 1
def r151fH (_ : Nat) : Nat := 4
def r151fBurnRow (k e : Nat) : Nat := e + k
def r151fLowCol (k s : Nat) : Nat := 2 * (10 * k - 1 - s)

/-- The frame is a strict first failure with unbounded defect. -/
theorem r151f_first_failure_frame {k : Nat} (hk : 4 <= k) :
    1 <= r151fQ k /\
      r151fR k < r151fQ k + 3 /\
      r151fV k = r151fQ k + 3 /\
      r151fG k + 1 < r151fR k /\
      2 < r151fG k + 1 /\
      r151fH k <= r151fQ k /\
      r151fH k <= r151fG k /\
      r151fR k - (r151fG k + 1) = k - 1 := by
  simp [r151fQ, r151fR, r151fV, r151fG, r151fH]
  omega

/-- The terminal burn row is early by an unbounded margin. -/
theorem r151f_terminal_burn_is_early {k : Nat} (hk : 4 <= k) :
    r151fR k <= r151fA k /\
      r151fA k < r151fQ k /\
      r151fQ k - r151fA k = k - 2 /\
      r151fBurnRow k (r151fR k - 1) = r151fA k := by
  simp [r151fR, r151fA, r151fQ, r151fBurnRow]
  omega

/-- The burn ladder is adjacent and strictly increasing, each band column
is consumed strictly above itself, strictly above the freeze row of the
frame, and strictly below the terminal witness. -/
theorem r151f_burn_ladder {k e : Nat} (hk : 4 <= k)
    (he0 : r151fG k < e) (he1 : e < r151fR k - 1) :
    e < r151fBurnRow k e /\
      r151fR k < r151fBurnRow k e /\
      r151fBurnRow k e < r151fA k /\
      r151fBurnRow k (e + 1) = r151fBurnRow k e + 1 := by
  simp [r151fG, r151fR, r151fA, r151fBurnRow] at he0 he1 ⊢
  omega

/-- The all-low tail: every row strictly between the terminal burn and the
blocker hosts at an owner-covered column, with the exact column-0 and
column-2 rail endpoints, the lag-three preview at `H`, and a tight cell
ceiling. -/
theorem r151f_low_tail {k s : Nat} (hk : 4 <= k)
    (hs0 : r151fA k < s) (hs1 : s < r151fV k) :
    r151fLowCol k s <= r151fG k /\
      r151fLowCol k s <= s /\
      r151fV k <= s + r151fLowCol k s + 1 /\
      (s = r151fV k - 1 -> r151fLowCol k s = 0) /\
      (s = r151fV k - 2 -> r151fLowCol k s = 2) /\
      (s = r151fQ k -> r151fLowCol k s = r151fH k) := by
  simp [r151fA, r151fV, r151fG, r151fQ, r151fH, r151fLowCol] at hs0 hs1 ⊢
  omega

/-- Host injectivity across the whole assignment: the low tail is strictly
decreasing in the row, and low columns are disjoint from the band. -/
theorem r151f_hosts_injective {k s₁ s₂ : Nat} (hk : 4 <= k)
    (hs₁0 : r151fA k < s₁) (hs₁1 : s₁ < r151fV k)
    (_hs₂0 : r151fA k < s₂) (hs₂1 : s₂ < r151fV k)
    (h12 : s₁ < s₂) :
    r151fLowCol k s₂ < r151fLowCol k s₁ /\
      r151fLowCol k s₁ < r151fG k + 1 := by
  simp [r151fA, r151fV, r151fG, r151fLowCol] at hs₁0 hs₁1 hs₂1 ⊢
  omega

/-- Every pre-freeze row strictly above the frame's freeze row is hosted
exactly once: it is a burn row of a unique band column or a low-tail row. -/
theorem r151f_every_row_hosted {k s : Nat} (hk : 4 <= k)
    (hs0 : r151fR k < s) (hs1 : s < r151fV k) :
    (s <= r151fA k /\
      r151fG k < s - k /\ s - k <= r151fR k - 1 /\
      r151fBurnRow k (s - k) = s) \/
    (r151fA k < s) := by
  by_cases hcase : s <= r151fA k
  · left
    simp [r151fR, r151fV, r151fA, r151fG, r151fBurnRow] at hs0 hs1 hcase ⊢
    omega
  · right
    omega

/-- The R148-era scalar interfaces all hold on the frame: exact midpoint,
PiZero at the freeze, exact FCROSS split, the ordered-HCR endpoint, and
the two-packet capacity bill. -/
theorem r151f_scalar_interfaces {k : Nat} (hk : 4 <= k) :
    r151fV k + 4 * k = 2 * r151fG k /\
      r151fR k + 1 = 2 * (4 * k + 1) - 1 /\
      r151fV k = 6 * k + 4 * k /\
      r151fV k + 4 * k <= 2 * r151fR k + 1 /\
      (r151fV k - r151fR k - 1) + 4 * k <= r151fR k := by
  simp [r151fV, r151fG, r151fR]
  omega

#print axioms gameF_ownerCovered_full_saturation
#print axioms gameF_band_cell_trichotomy
#print axioms gameF_band_host_no_skip
#print axioms gameF_band_burn_first_use_increases
#print axioms gameF_earlyTP_burns_band
#print axioms gameF_earlyTP_forces_low_tail
#print axioms gameF_firstFailure_burn_ladder_normal_form
#print axioms gameF_upperRail_of_postExhaustionDeadline
#print axioms r151f_first_failure_frame
#print axioms r151f_terminal_burn_is_early
#print axioms r151f_burn_ladder
#print axioms r151f_low_tail
#print axioms r151f_hosts_injective
#print axioms r151f_every_row_hosted
#print axioms r151f_scalar_interfaces

end ChompLean
