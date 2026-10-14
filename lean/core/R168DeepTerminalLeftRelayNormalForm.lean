import R165DeepTerminalOwnerDescentReduction

set_option autoImplicit false

namespace ChompLean

/-!
# Deep terminal history: strict-left relay and the surviving owner braid

Write `c=r-1` and `q=v-3`.  If `v` freezes at `r` but already occurs at
`(a,c)` with `a<q`, row-start propagation gives a host of `v` on every later
pre-freeze row.  The old host at `c` makes `v` a member of every later source
in that column, so none of those later hosts can remain at `c`.  Fixed-row
injectivity therefore sharpens the propagation conclusion from `<r` to
`<c` immediately.

This is a genuine all-depth consequence of the actual recurrence.  It shows
that a hypothetical deep live terminal packet contains a strict-left target
relay on every row through the preview row.  The remaining owner-descent
debt is now an exact braid exclusion: this left-moving `v` relay must be
shown incompatible with a left opening owner of `q`.
-/

/-- A target already hosted in the terminal predecessor column must rehost
strictly to the left of that column on every later row before its row start.
The strictness is stronger than the raw `<r` supplied by
`rowStartPropagation`; equality with `r-1` is excluded by same-lower
no-repeat. -/
theorem gameF_deep_terminal_target_rehosts_strictly_left
    {v r a t : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra : r <= a)
    (hat : a < t)
    (htv : t < v)
    (hhost : gameF a (r - 1) = v) :
    exists b, b < r - 1 /\ gameF t b = v := by
  rcases rowStartPropagation gameRecurrenceModel hstart hrv
      (by omega : r < t) htv with ⟨b, hbr, hbhost⟩
  have hbc : b <= r - 1 := by omega
  have hbne : b ≠ r - 1 := by
    intro hbcEq
    subst b
    exact encoding_same_lower_no_repeat game_encodes
      (s := r - 1) (t₁ := a) (t₂ := t) (p := v)
      (by omega) hat htv hhost hbhost
  exact ⟨b, by omega, hbhost⟩

/-- Preview-row specialization: every genuinely deep terminal host creates
an actual host of `v` strictly left of the terminal predecessor on row
`q=v-3`. -/
theorem gameF_deep_terminal_target_preview_relay
    {v r a : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra : r <= a)
    (hadeep : a + 3 < v)
    (hhost : gameF a (r - 1) = v) :
    exists H, H < r - 1 /\ H <= v - 3 /\ gameF (v - 3) H = v := by
  rcases gameF_deep_terminal_target_rehosts_strictly_left
      hrv hstart hra (by omega : a < v - 3) (by omega)
      hhost with ⟨H, hHc, hHhost⟩
  exact ⟨H, hHc, by omega, hHhost⟩

/-- Any separately named preview host is the propagated one, by fixed-row
injectivity.  Thus a deep terminal host alone forces that preview host
strictly left of the predecessor column. -/
theorem gameF_deep_terminal_named_preview_host_strictly_left
    {v r a H : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra : r <= a)
    (hadeep : a + 3 < v)
    (hhost : gameF a (r - 1) = v)
    (hHq : H <= v - 3)
    (hpreview : gameF (v - 3) H = v) :
    H < r - 1 := by
  rcases gameF_deep_terminal_target_preview_relay
      hrv hstart hra hadeep hhost with ⟨b, hbc, hbq, hbhost⟩
  have hHb : H = b :=
    gameRecurrenceModel.fixed_q_injective hHq hbq
      (hpreview.trans hbhost.symm)
  simpa [hHb] using hbc

/-- Full vertical packet exported by a live deep terminal host.  Every cell
from the old host through row `v-1` is a high MEX cell.  On every later row,
the target `v` is already in the predecessor-column source and has a genuine
strict-left current-row relay. -/
theorem gameF_deep_live_terminal_vertical_relay_packet
    {v r a : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra : r <= a)
    (hhost : gameF a (r - 1) = v)
    (hlive : ColumnLiveBelow v (r - 1)) :
    (forall t, a <= t -> t < v ->
      IsMex (B gameF t (r - 1)) (gameF t (r - 1)) /\
        t < gameF t (r - 1)) /\
    (forall t, a < t -> t < v ->
      B gameF t (r - 1) v /\
        gameF t (r - 1) ≠ v /\
        exists b, b < r - 1 /\ gameF t b = v) := by
  constructor
  · intro t hat htv
    exact ⟨gameF_cell_isMex_of_columnLiveBelow hlive (by omega) htv,
      gameF_cell_above_row_of_columnLiveBelow hlive (by omega) htv⟩
  · intro t hat htv
    have hBv : B gameF t (r - 1) v := by
      left
      refine ⟨a, hat, ?_⟩
      have hca : r - 1 <= a := by omega
      simpa [Nat.min_eq_right hca] using hhost
    have hmex : IsMex (B gameF t (r - 1)) (gameF t (r - 1)) :=
      gameF_cell_isMex_of_columnLiveBelow hlive (by omega) htv
    have hne : gameF t (r - 1) ≠ v := by
      intro heq
      apply hmex.2.1
      simpa [heq] using hBv
    exact ⟨hBv, hne,
      gameF_deep_terminal_target_rehosts_strictly_left
        hrv hstart hra hat htv hhost⟩

/-- A left diagonal or row-start owner of the preview value is literally
visible in the preview source at the terminal predecessor. -/
theorem gameF_preview_left_opening_owner_enters_source
    {v c : Nat}
    (hcv : c < v - 3) :
    ((exists d, d < c /\ gameF d d = v - 3) \/
      (exists s, s < c /\ s < v - 3 /\ gameF (v - 3) s = v - 3)) ->
    B gameF (v - 3) c (v - 3) := by
  intro howner
  rcases howner with ⟨d, hdc, hdiag⟩ | ⟨s, hsc, hsq, hrow⟩
  · left
    refine ⟨d, by omega, ?_⟩
    simpa [Nat.min_eq_left (Nat.le_of_lt hdc)] using hdiag
  · right
    exact ⟨s, hsc, hrow⟩

/-- In a failed owner-covered band the preview source necessarily contains
`q=v-3` through an actual left opening owner.  This is the exact surviving
side of the braid: the deep terminal relay puts `v` in the same prefix,
while owner coverage puts `q` in the source. -/
theorem gameF_failed_band_has_left_preview_owner_in_source
    {v r g : Nat}
    (hv : 7 <= v)
    (hrq : r <= v - 3)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r) :
    ((exists d, d <= g /\ d < r - 1 /\ gameF d d = v - 3) \/
      (exists s, s <= g /\ s < r - 1 /\ s < v - 3 /\
        gameF (v - 3) s = v - 3)) /\
      B gameF (v - 3) (r - 1) (v - 3) := by
  have hqpos : 0 < v - 3 := by omega
  have hqv : v - 3 < v := by omega
  rcases howners (v - 3) hqpos hqv with
      ⟨d, hdg, hdiag⟩ | ⟨s, hsg, hsq, hrow⟩
  · have harm : (exists d, d <= g /\ d < r - 1 /\
        gameF d d = v - 3) \/
      (exists s, s <= g /\ s < r - 1 /\ s < v - 3 /\
        gameF (v - 3) s = v - 3) :=
      Or.inl ⟨d, hdg, by omega, hdiag⟩
    refine ⟨harm, ?_⟩
    exact gameF_preview_left_opening_owner_enters_source
      (by omega) (Or.inl ⟨d, by omega, hdiag⟩)
  · have harm : (exists d, d <= g /\ d < r - 1 /\
        gameF d d = v - 3) \/
      (exists s, s <= g /\ s < r - 1 /\ s < v - 3 /\
        gameF (v - 3) s = v - 3) :=
      Or.inr ⟨s, hsg, by omega, hsq, hrow⟩
    refine ⟨harm, ?_⟩
    exact gameF_preview_left_opening_owner_enters_source
      (by omega) (Or.inr ⟨s, by omega, hsq, hrow⟩)

/-- The source-hole condition implies the desired all-depth owner descent.
It excludes every column-tail occurrence of the preview value as well as
left opening owners. No actual-game separation proving strictness is supplied. -/
def LiveDeepTerminalPreviewSourceHole : Prop :=
  forall {v r a : Nat},
    7 <= v ->
    r < v ->
    gameF v r = v ->
    2 < r - 1 ->
    r <= a ->
    a + 3 < v ->
    gameF a (r - 1) = v ->
    ColumnLiveBelow v (r - 1) ->
    Not (B gameF (v - 3) (r - 1) (v - 3))

theorem liveDeepTerminalPreviewOwnerNotLeft_of_sourceHole
    (hhole : LiveDeepTerminalPreviewSourceHole) :
    LiveDeepTerminalPreviewOwnerNotLeft := by
  intro v r a hv hrv hstart hc hra hadeep hhost hlive
  have hnotB := hhole hv hrv hstart hc hra hadeep hhost hlive
  constructor
  · intro d hdiag
    apply Nat.le_of_not_gt
    intro hdc
    apply hnotB
    exact gameF_preview_left_opening_owner_enters_source
      (by omega) (Or.inl ⟨d, hdc, hdiag⟩)
  · intro s hsq hrow
    apply Nat.le_of_not_gt
    intro hsc
    apply hnotB
    exact gameF_preview_left_opening_owner_enters_source
      (by omega) (Or.inr ⟨s, hsc, hsq, hrow⟩)

/-! ## Exact completed-history edit forced by a left owner -/

/-- A value whose diagonal owner lies strictly left of a column never occurs
in that exact column at any later row.  ECHO-LEFT points every such later
occurrence back strictly left of the owner. -/
theorem gameF_left_diagonal_owner_absent_from_column_history
    {z d top c : Nat}
    (hdc : d < c)
    (hdiag : gameF d d = z) :
    Not (ColHistPred gameF top c z) := by
  rintro ⟨t, hct, _httop, hhost⟩
  have hleft := gameF_past_diagonal_echo_strictly_left
    (a := d) (q := t) (r := c) (by omega) hct
    (hhost.trans hdiag.symm)
  omega

/-- The same exact-column exclusion for a row-start owner strictly left of
the column.  Before the birth row, row-start propagation rehosts the value
strictly left of its owner; from the birth row onward, persistence and
fixed-row injectivity pin the unique host to the owner column. -/
theorem gameF_left_rowstart_owner_absent_from_column_history
    {z s top c : Nat}
    (hsz : s < z)
    (hstart : gameF z s = z)
    (hsc : s < c) :
    Not (ColHistPred gameF top c z) := by
  rintro ⟨t, hct, _httop, hhost⟩
  by_cases htz : t < z
  · rcases rowStartPropagation gameRecurrenceModel hstart hsz
        (by omega : s < t) htz with ⟨b, hbs, hbhost⟩
    have hbc : b = c :=
      gameRecurrenceModel.fixed_q_injective (by omega) hct
        (hbhost.trans hhost.symm)
    omega
  · have hzt : z <= t := Nat.le_of_not_gt htz
    have hpersist : gameF t s = z :=
      gameF_freeze_persists hsz hstart hzt
    have hscEq : s = c :=
      gameRecurrenceModel.fixed_q_injective (by omega) hct
        (hpersist.trans hhost.symm)
    omega

/-- Before a row-start value is born, its own eventual freeze column has no
completed occurrence of that value. -/
theorem gameF_terminal_target_absent_from_freeze_column_history
    {v r : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v) :
    Not (ColHistPred gameF v r v) := by
  rintro ⟨t, hrt, htv, hhost⟩
  by_cases hrtStrict : r < t
  · rcases rowStartPropagation gameRecurrenceModel hstart hrv
        hrtStrict htv with ⟨b, hbr, hbhost⟩
    have hbrEq : b = r :=
      gameRecurrenceModel.fixed_q_injective (by omega) hrt
        (hbhost.trans hhost.symm)
    omega
  · have htr : t = r := by omega
    subst t
    exact disjoint_D_S gameRecurrenceModel
      ⟨r, hhost⟩ ⟨r, hrv, hstart⟩

/-- Exact two-label history edit normal form under the bad left-owner arm.
The terminal target `v` is present in completed history at `c=r-1` and
absent at the freeze column `r`.  In contrast, the preview value `q=v-3`
is absent from both exact column histories when its opening owner is left of
`c`.

This explains the new edit census structurally.  A hypothetical deep live
left-owner packet would belong to the same `remove-v, keep-q-absent` edit
class as the ordinary age-three packets.  Thus edit cardinality alone does
not prove the descent; the remaining useful history statement is precisely
that this edit class forces the old host to be the age-three row. -/
theorem gameF_deep_terminal_leftOwner_history_edit_normalForm
    {v r a : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra : r <= a)
    (hadeep : a + 3 < v)
    (hhost : gameF a (r - 1) = v)
    (howner :
      (exists d, d < r - 1 /\ gameF d d = v - 3) \/
      (exists s, s < r - 1 /\ s < v - 3 /\
        gameF (v - 3) s = v - 3)) :
    ColHistPred gameF v (r - 1) v /\
      Not (ColHistPred gameF v r v) /\
      Not (ColHistPred gameF v (r - 1) (v - 3)) /\
      Not (ColHistPred gameF v r (v - 3)) := by
  have hvOld : ColHistPred gameF v (r - 1) v :=
    ⟨a, by omega, by omega, hhost⟩
  have hvNew : Not (ColHistPred gameF v r v) :=
    gameF_terminal_target_absent_from_freeze_column_history hrv hstart
  rcases howner with ⟨d, hdc, hdiag⟩ | ⟨s, hsc, hsq, hrow⟩
  · exact ⟨hvOld, hvNew,
      gameF_left_diagonal_owner_absent_from_column_history hdc hdiag,
      gameF_left_diagonal_owner_absent_from_column_history
        (by omega : d < r) hdiag⟩
  · exact ⟨hvOld, hvNew,
      gameF_left_rowstart_owner_absent_from_column_history hsq hrow hsc,
      gameF_left_rowstart_owner_absent_from_column_history
        hsq hrow (by omega : s < r)⟩

/-! ## A weaker history-edit target sufficient for owner descent -/

/-- History-classified live terminal law.  Unlike
`LiveTerminalPredecessorLag3`, this asserts age three only in the edit class
where the preview value `q=v-3` is absent from both completed histories at
the terminal predecessor and at the freeze column.

Every bad left-owner arm lies in this class by the preceding theorems, so
this restricted statement is already sufficient for the desired all-depth
owner descent. -/
def LiveTerminalPreviewAbsentHistoryForcesLag3 : Prop :=
  forall {v r a : Nat},
    7 <= v ->
    r < v ->
    gameF v r = v ->
    2 < r - 1 ->
    r <= a ->
    a < v ->
    gameF a (r - 1) = v ->
    ColumnLiveBelow v (r - 1) ->
    Not (ColHistPred gameF v (r - 1) (v - 3)) ->
    Not (ColHistPred gameF v r (v - 3)) ->
    a + 3 = v

/-- The unrestricted live age-three law implies the history-classified
version immediately. -/
theorem liveTerminalPreviewAbsentHistoryForcesLag3_of_liveTerminalPredecessorLag3
    (hliveLag3 : LiveTerminalPredecessorLag3) :
    LiveTerminalPreviewAbsentHistoryForcesLag3 := by
  intro v r a hv hrv hstart hc hra hav hhost hlive _hqOld _hqNew
  exact hliveLag3 hv hrv hstart hc hra hav hhost hlive

/-- The new history-classified law is already enough for the all-depth owner
descent.  If a diagonal or row-start owner of `q` were left of `c=r-1`, the
preview value would be absent from both exact column histories.  The
classified law would then force age three, contradicting the genuinely deep
host premise. -/
theorem liveDeepTerminalPreviewOwnerNotLeft_of_previewAbsentHistoryForcesLag3
    (hage : LiveTerminalPreviewAbsentHistoryForcesLag3) :
    LiveDeepTerminalPreviewOwnerNotLeft := by
  intro v r a hv hrv hstart hc hra hadeep hhost hlive
  constructor
  · intro d hdiag
    apply Nat.le_of_not_gt
    intro hdc
    have hqOld : Not (ColHistPred gameF v (r - 1) (v - 3)) :=
      gameF_left_diagonal_owner_absent_from_column_history hdc hdiag
    have hqNew : Not (ColHistPred gameF v r (v - 3)) :=
      gameF_left_diagonal_owner_absent_from_column_history
        (by omega : d < r) hdiag
    have hage3 := hage hv hrv hstart hc hra (by omega) hhost hlive
      hqOld hqNew
    omega
  · intro s hsq hrow
    apply Nat.le_of_not_gt
    intro hsc
    have hqOld : Not (ColHistPred gameF v (r - 1) (v - 3)) :=
      gameF_left_rowstart_owner_absent_from_column_history hsq hrow hsc
    have hqNew : Not (ColHistPred gameF v r (v - 3)) :=
      gameF_left_rowstart_owner_absent_from_column_history
        hsq hrow (by omega : s < r)
    have hage3 := hage hv hrv hstart hc hra (by omega) hhost hlive
      hqOld hqNew
    omega

/-- Minimal adjacent-history exchange formulation.  When `q=v-3` is absent
from both exact histories, a live terminal edge must have no target `v`
history below row `q` in its predecessor column.  Causal depth then leaves
only the row-`q` host.

This is the precise missing bridge not supplied by the existing
`gameF_colHist_causal_depth_three`: that theorem exposes the old-history arm
but deliberately does not eliminate it. -/
def LiveTerminalPreviewAbsentExcludesOldTargetHistory : Prop :=
  forall {v r : Nat},
    7 <= v ->
    r < v ->
    gameF v r = v ->
    2 < r - 1 ->
    ColumnLiveBelow v (r - 1) ->
    Not (ColHistPred gameF v (r - 1) (v - 3)) ->
    Not (ColHistPred gameF v r (v - 3)) ->
    Not (ColHistPred gameF (v - 3) (r - 1) v)

/-- The history-classified age-three law is exactly equivalent to the
minimal old-target exchange exclusion. -/
theorem liveTerminalPreviewAbsentHistoryForcesLag3_iff_exchange :
    LiveTerminalPreviewAbsentHistoryForcesLag3 <->
      LiveTerminalPreviewAbsentExcludesOldTargetHistory := by
  constructor
  · intro hage v r hv hrv hstart hc hlive hqOld hqNew hold
    rcases hold with ⟨a, hca, haq, hhost⟩
    have hra : r <= a := by
      apply Nat.le_of_not_gt
      intro har
      have ha : a = r - 1 := by omega
      subst a
      exact disjoint_D_S gameRecurrenceModel
        ⟨r - 1, hhost⟩ ⟨r, hrv, hstart⟩
    have hage3 := hage hv hrv hstart hc hra (by omega) hhost hlive
      hqOld hqNew
    omega
  · intro hexchange v r a hv hrv hstart hc hra hav hhost hlive
      hqOld hqNew
    have hfull : ColHistPred gameF v (r - 1) v :=
      ⟨a, by omega, hav, hhost⟩
    have hvEq : v - 3 + 3 = v := by omega
    have hfull' :
        ColHistPred gameF (v - 3 + 3) (r - 1) (v - 3 + 3) := by
      simpa [hvEq] using hfull
    have hqhost : gameF (v - 3) (r - 1) = v := by
      rcases (gameF_colHist_causal_depth_three
          (q := v - 3) (c := r - 1) (by omega) hc).mp hfull' with
          hold | hnew
      · have hold' : ColHistPred gameF (v - 3) (r - 1) v := by
          simpa [hvEq] using hold
        exact False.elim
          ((hexchange hv hrv hstart hc hlive hqOld hqNew) hold')
      · simpa [hvEq] using hnew.2
    by_cases haq : a < v - 3
    · exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          (s := r - 1) (t₁ := a) (t₂ := v - 3) (p := v)
          (by omega) haq (by omega) hhost hqhost)
    · have hacases : a = v - 3 \/ a = v - 2 \/ a = v - 1 := by
        omega
      rcases hacases with ha | ha | ha
      · omega
      · have hcol : r - 1 = 2 := by
          have hhost' : gameF (v - 2) (r - 1) = (v - 2) + 2 := by
            rw [show (v - 2) + 2 = v by omega]
            simpa [ha] using hhost
          apply gameF_lag_two_host_only_col2
            (q := v - 2) (by omega) (by omega) hhost'
        omega
      · have hcol : r - 1 = 0 := by
          have hhost' : gameF ((v - 2) + 1) (r - 1) = (v - 2) + 2 := by
            rw [show (v - 2) + 1 = v - 1 by omega,
              show (v - 2) + 2 = v by omega]
            simpa [ha] using hhost
          apply gameF_lag_one_host_only_col0
            (q := v - 2) (by omega) hhost'
        omega

/-- The minimal adjacent-history exchange closes the assignment upper rail
directly.  The equivalence above turns it into the classified age-three law;
that law gives all-depth preview-owner descent, which is exactly the final
input of the R165 upper-rail reduction. -/
theorem gameF_upperRail_of_previewAbsentExcludesOldTargetHistory
    {q r g H : Nat}
    (hq : 4 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hexchange : LiveTerminalPreviewAbsentExcludesOldTargetHistory) :
    r <= g + 1 := by
  apply gameF_upperRail_of_liveDeepTerminalPreviewOwnerNotLeft
    hq hrv hstart howners hinterior hpreviewLe hpreviewLeft hpreview
  apply liveDeepTerminalPreviewOwnerNotLeft_of_previewAbsentHistoryForcesLag3
  exact liveTerminalPreviewAbsentHistoryForcesLag3_iff_exchange.mpr hexchange

#print axioms gameF_deep_terminal_target_rehosts_strictly_left
#print axioms gameF_deep_terminal_target_preview_relay
#print axioms gameF_deep_terminal_named_preview_host_strictly_left
#print axioms gameF_deep_live_terminal_vertical_relay_packet
#print axioms gameF_preview_left_opening_owner_enters_source
#print axioms gameF_failed_band_has_left_preview_owner_in_source
#print axioms liveDeepTerminalPreviewOwnerNotLeft_of_sourceHole
#print axioms gameF_left_diagonal_owner_absent_from_column_history
#print axioms gameF_left_rowstart_owner_absent_from_column_history
#print axioms gameF_terminal_target_absent_from_freeze_column_history
#print axioms gameF_deep_terminal_leftOwner_history_edit_normalForm
#print axioms liveTerminalPreviewAbsentHistoryForcesLag3_of_liveTerminalPredecessorLag3
#print axioms liveDeepTerminalPreviewOwnerNotLeft_of_previewAbsentHistoryForcesLag3
#print axioms liveTerminalPreviewAbsentHistoryForcesLag3_iff_exchange
#print axioms gameF_upperRail_of_previewAbsentExcludesOldTargetHistory

end ChompLean
