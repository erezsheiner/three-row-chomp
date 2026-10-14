import R163Lag8PreviewOwnerOrderReduction

set_option autoImplicit false

namespace ChompLean

/-!
# Deep terminal history: fixed lag ten versus an all-depth owner descent

After the proved lag-four through lag-seven and lag-nine rail exclusions,
and the conditional lag-eight owner-order exclusion, the first remaining
endpoint is target lag ten.  It is not represented by an affine fixed-column
rail.  The first definition below records the exact fixed-depth analogue of
the lag-eight owner-order atom.

Proving one such atom per missing affine offset would not terminate the
argument.  The second definition is the all-depth statement actually needed:
on a live terminal-predecessor column, every genuinely old target host forces
the opening owner of the preview value `v-3` to lie at or to the right of that
column.  Owner coverage supplies the opposite inequality in a first-failure
frame, so this one descent atom closes every depth at once.
-/

/-- The exact lag-ten slice parallel to `Lag8PreviewOwnerNotLeft`.  This is
an explicit proposed chronology atom, not a theorem asserted for `gameF`. -/
def Lag10PreviewOwnerNotLeft : Prop :=
  forall {v r : Nat},
    13 <= v ->
    r < v ->
    gameF v r = v ->
    r <= v - 10 ->
    gameF (v - 10) (r - 1) = v ->
    (forall a, gameF a a = v - 3 -> r - 1 <= a) /\
    (forall s, s < v - 3 -> gameF (v - 3) s = v - 3 -> r - 1 <= s)

/-- All-depth owner descent, restricted to the only columns relevant to a
first failure: live terminal-predecessor columns.  Compared with
`LiveTerminalPredecessorLag3`, this does not forbid an old host outright; it
only transports the opening owner of `v-3` to the host column or farther
right. -/
def LiveDeepTerminalPreviewOwnerNotLeft : Prop :=
  forall {v r a : Nat},
    7 <= v ->
    r < v ->
    gameF v r = v ->
    2 < r - 1 ->
    r <= a ->
    a + 3 < v ->
    gameF a (r - 1) = v ->
    ColumnLiveBelow v (r - 1) ->
    (forall d, gameF d d = v - 3 -> r - 1 <= d) /\
    (forall s, s < v - 3 -> gameF (v - 3) s = v - 3 -> r - 1 <= s)

/-- The fixed lag-ten owner-order bit contradicts an owner-covered failed
band for the same reason as its lag-eight counterpart. -/
theorem gameF_lag10_failed_band_impossible_of_previewOwnerNotLeft
    {v r g : Nat}
    (hv : 13 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 10)
    (hburn : gameF (v - 10) (r - 1) = v)
    (horder : Lag10PreviewOwnerNotLeft) :
    False := by
  have hqpos : 0 < v - 3 := by omega
  have hqv : v - 3 < v := by omega
  have hnotLeft := horder hv hrv hstart hra hburn
  rcases howners (v - 3) hqpos hqv with
      ⟨a, hag, hdiag⟩ | ⟨s, hsg, hsq, hrow⟩
  · have hca : r - 1 <= a := hnotLeft.1 a hdiag
    omega
  · have hcs : r - 1 <= s := hnotLeft.2 s hsq hrow
    omega

/-- Thus a separate lag-ten atom advances the normal form by exactly one
row: from target lag at least ten to target lag at least eleven. -/
theorem gameF_firstFailure_burn_ladder_pre_lag11_of_lag8_lag10_ownerNotLeft
    {q r g H : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hlag8 : Lag8PreviewOwnerNotLeft)
    (hlag10 : Lag10PreviewOwnerNotLeft) :
    exists a, r <= a /\ a < q - 7 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_pre_lag10_of_previewOwnerNotLeft
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview hlag8 with
      ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 7
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have ha : a = q - 7 := by omega
    subst a
    have hburn10 : gameF ((q + 3) - 10) (r - 1) = q + 3 := by
      have hidx : (q + 3) - 10 = q - 7 := by omega
      rw [hidx]
      exact hburn
    exact False.elim
      (gameF_lag10_failed_band_impossible_of_previewOwnerNotLeft
        (v := q + 3) (r := r) (g := g)
        (by omega) hrv hstart howners hfailure (by omega) hburn10 hlag10)

/-- The earlier old-history-to-preview-freeze atom also implies the owner
descent, and does so without using the liveness premise.  Once `v-3` freezes
at the terminal predecessor, diagonal ownership is disjoint and any other
row-start owner is the same column by row injectivity. -/
theorem liveDeepTerminalPreviewOwnerNotLeft_of_terminalOldHistoryFreeze
    (hOldFreeze : TerminalOldHistoryForcesLag3Freeze) :
    LiveDeepTerminalPreviewOwnerNotLeft := by
  intro v r a hv hrv hstart hc hra hadeep hhost _hlive
  have hhist : ColHistPred gameF (v - 3) (r - 1) v := by
    exact ⟨a, by omega, by omega, hhost⟩
  have hqfreeze : gameF (v - 3) (r - 1) = v - 3 :=
    hOldFreeze hrv hstart hc hhist
  constructor
  · intro d hdiag
    exfalso
    exact disjoint_D_S gameRecurrenceModel
      ⟨d, hdiag⟩ ⟨r - 1, by omega, hqfreeze⟩
  · intro s hsq hrow
    have hsc : s = r - 1 :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hsq) (by omega) (hrow.trans hqfreeze.symm)
    omega

/-- The live lag-three law implies the weaker all-depth owner descent:
under its hypotheses a genuinely old live-column host is already
impossible. -/
theorem liveDeepTerminalPreviewOwnerNotLeft_of_liveTerminalPredecessorLag3
    (hliveLag3 : LiveTerminalPredecessorLag3) :
    LiveDeepTerminalPreviewOwnerNotLeft := by
  intro v r a hv hrv hstart hc hra hadeep hhost hlive
  have heq : a + 3 = v :=
    hliveLag3 hv hrv hstart hc hra (by omega) hhost hlive
  omega

/-- The all-depth owner descent closes the upper rail directly, before any
finite lag sieve.  At a strict failure, R137 supplies a genuinely old host;
lower-owner coverage makes its column live and also supplies an opening
owner of `v-3` to the left.  The descent atom forces that same owner to the
right. -/
theorem gameF_upperRail_of_liveDeepTerminalPreviewOwnerNotLeft
    {q r g H : Nat}
    (hq : 4 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hdescent : LiveDeepTerminalPreviewOwnerNotLeft) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  rcases gameF_firstFailure_forces_early_terminal_sighting
      (by omega) hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hhost⟩
  have hc : 2 < r - 1 := by omega
  have hlive : ColumnLiveBelow (q + 3) (r - 1) :=
    lowerOwnerCoveredBy_columnLive_right_of_cutoff howners (by omega)
  have hnotLeft := hdescent
    (v := q + 3) (r := r) (a := a)
    (by omega) hrv hstart hc hra (by omega) hhost hlive
  rcases howners q (by omega) (by omega) with
      ⟨d, hdg, hdiag⟩ | ⟨s, hsg, hsq, hrow⟩
  · have hcd : r - 1 <= d := by
      apply hnotLeft.1 d
      simpa using hdiag
    omega
  · have hcs : r - 1 <= s := by
      apply hnotLeft.2 s
      · simpa using hsq
      · simpa using hrow
    omega

/-- Once the lag-eight owner-order endpoint is removed, the depth-eight
history bound eliminates the entire deeper branch.  This is the clean
finite-depth alternative to proving one owner-order atom for lag ten,
thirteen, eighteen, and so on. -/
theorem gameF_upperRail_of_historyDepth8_and_lag8PreviewOwnerNotLeft
    {q r g H : Nat}
    (hq : 23 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hdepth8 : TerminalTargetHistoryDepth8)
    (hlag8 : Lag8PreviewOwnerNotLeft) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  rcases gameF_firstFailure_terminal_burn_exact_lag8_of_historyDepth8
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview hdepth8 with
      ⟨a, ha, hra, hburn, _hband, _htail⟩
  have hburn8 : gameF ((q + 3) - 8) (r - 1) = q + 3 := by
    rw [ha] at hburn
    have hidx : (q + 3) - 8 = q - 5 := by omega
    rw [hidx]
    exact hburn
  exact gameF_lag8_failed_band_impossible_of_previewOwnerNotLeft
    (v := q + 3) (r := r) (g := g)
    (by omega) hrv hstart howners hfailure (by omega) hburn8 hlag8

#print axioms gameF_lag10_failed_band_impossible_of_previewOwnerNotLeft
#print axioms gameF_firstFailure_burn_ladder_pre_lag11_of_lag8_lag10_ownerNotLeft
#print axioms liveDeepTerminalPreviewOwnerNotLeft_of_terminalOldHistoryFreeze
#print axioms liveDeepTerminalPreviewOwnerNotLeft_of_liveTerminalPredecessorLag3
#print axioms gameF_upperRail_of_liveDeepTerminalPreviewOwnerNotLeft
#print axioms gameF_upperRail_of_historyDepth8_and_lag8PreviewOwnerNotLeft

end ChompLean
